

use crate::mlsparser::{*};
use crate::nftabuilder::{*};
use crate::spec::{*};
use crate::debug::{*};

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;
use std::mem::take;

use std::fs::read_to_string;

use Type::{*};
use Value::{*};
use Program::{*};
use Line::{*};
use SpecType::{*};
use ProcValue::{*};
use ProcType::{*};
use SpecVariant::{*};
use RefineLiteral::{*};
use Constname::{*};




#[derive(Clone,Debug)]
pub enum ProcPattern {
    LPat(Box<ProcPattern>),
    RPat(Box<ProcPattern>),
    PairPat(Box<ProcPattern>,Box<ProcPattern>),
    Unit,
    VarPat(String)
}
use ProcPattern::{*};

#[derive(Clone,PartialEq,Eq)]
pub enum Dsl {
    RecursivePlaceholder,

    TransferStack(Box<Dsl>,usize),
    AccessStack(usize),
    ApplyStack(Box<Dsl>,Vec<Dsl>),

    Lside(Box<Dsl>),
    Rside(Box<Dsl>),
    Pair(Box<Dsl>,Box<Dsl>),
    BaseValue(usize),
    
    SwitchValue(Box<Dsl>,Box<Dsl>,Box<Dsl>),
    LUndo(Box<Dsl>),
    RUndo(Box<Dsl>),
    LeftValue(Box<Dsl>),
    RightValue(Box<Dsl>),

    EqProg(Box<Dsl>,Box<Dsl>),
    NeqProg(Box<Dsl>,Box<Dsl>)
}
use Dsl::{*};


pub enum SwitchShortResult {
    Undecided,
    SwitchLeft,
    SwitchRight,
    Die
}
use SwitchShortResult::{*};


impl ExpressionBuilder {
    pub fn get_transferstack(&mut self,a:Dsl,b:usize) -> Dsl {//this attempts eta-reduction, immensely helpful to the algorithm because of the function caches
        match a {
            ApplyStack(a,l) if l.len()==b => match *a {
                BaseValue(f)=>{
                    if l.iter().enumerate().all(|(i,x)|if let BaseValue(y)=x {i+*y==b-1} else {false}) {
                        BaseValue(f)
                    } else {
                        TransferStack(Box::new(ApplyStack(Box::new(BaseValue(f)),l)),b)
                    }
                },
                a=>TransferStack(Box::new(ApplyStack(Box::new(a),l)),b)
            },
            TransferStack(a,c) => TransferStack(a,c+b),
            a=>TransferStack(Box::new(a),b)
        }
    }
    pub fn get_applied(&mut self,a:Dsl,b:Vec<Dsl>) -> Dsl {
        if b.len()==0 {return a}
        match a {
            Pair(..)|Lside(..)|Rside(..) => {panic!("{:#?} {:#?}",a,b)},
            ApplyStack(a,b2) => self.get_applied(*a,b2.into_iter().chain(b.into_iter()).collect()),
            TransferStack(prog,amt)=>{
                let blen = b.len();
                let mut b=b.into_iter();
                let hooh = if amt>blen {amt-blen} else {0};
                let aa:Vec<_> = vec![(b.by_ref().take(amt).rev().map(|x|x).collect(),hooh)];
                let we = self.substitute(&*prog,hooh,0,Rc::new(aa));
                if amt<blen {self.get_applied(we,b.collect())}
                else if amt>blen {self.get_transferstack(we,hooh)}
                else {we}
            },
            BaseValue(f)=> match &self.values[f].0 {
                FuncAsValue(fo) => {
                    let fo=*fo;
                    if let Some(aa) = self.get_required_function_args(fo) {
                        if b.len()>=aa {
                            let mut okay = true;
                            let args = b.iter().take(aa).map(|x|if let BaseValue(y)=x {*y} else {okay=false;0}).collect();
                            if okay {
                                if b.len()==aa {
                                    return BaseValue(self.exec_function(fo,args))
                                }
                                return ApplyStack(Box::new(BaseValue(self.exec_function(fo,args))),b.into_iter().skip(aa).collect())
                            } 
                        }
                    }
                    ApplyStack(Box::new(BaseValue(f)),b)
                }
                _=>panic!("tried to apply arguments to a basevalue : {:?} {:?} {:?}",f,DebugValue{t:f,expr:self},b)
            },
            RecursivePlaceholder=>{
                if b.len()!=1 {panic!("this can be supported but isn't right now");}
                if let BaseValue(v) = &b[0] {
                    return BaseValue(self.exec_interior_recursive_function(*v));
                }
                ApplyStack(Box::new(RecursivePlaceholder),b)
            }
            f => ApplyStack(Box::new(f),b)
        }
    }
    pub fn get_left_value(&mut self,a:Dsl) -> Dsl {
        match a {
            Pair(a,_) => *a,
            BaseValue(a) => match &self.values[a].0 {
                Uneval => BaseValue(0),
                PairValue(a,_) => BaseValue(*a),
                _=>LeftValue(Box::new(BaseValue(a)))
            }
            a=>LeftValue(Box::new(a))
        }
    }
    pub fn get_right_value(&mut self,a:Dsl) -> Dsl {
        match a {
            Pair(_,a) => *a,
            BaseValue(a) => match &self.values[a].0 {
                Uneval => BaseValue(0),
                PairValue(_,a) => BaseValue(*a),
                _=>RightValue(Box::new(BaseValue(a)))
            }
            a=>RightValue(Box::new(a))
        }
    }
    pub fn get_pair_prog(&mut self,a:Dsl,b:Dsl) -> Dsl {
        match (a,b) {
            (BaseValue(a),BaseValue(b)) => BaseValue(self.get_pair(a,b)),
            (a,b) => Pair(Box::new(a),Box::new(b))
        }
    }
    pub fn get_l_prog(&mut self,a:Dsl) -> Dsl {
        match a {
            BaseValue(a) => BaseValue(self.get_l(a)),
            a => Lside(Box::new(a))
        }
    }
    pub fn get_r_prog(&mut self,a:Dsl) -> Dsl {
        match a {
            BaseValue(a) => BaseValue(self.get_r(a)),
            a => Rside(Box::new(a))
        }
    }
    pub fn get_undo_left(&self,a:Dsl) -> Dsl {
        match a {
            BaseValue(a) => match &self.values[a].0 {
                Uneval => BaseValue(0),
                LValue(v) => BaseValue(*v),
                _=>LUndo(Box::new(BaseValue(a)))
            }
            a=>LUndo(Box::new(a))
        }
    }
    pub fn get_undo_right(&self,a:Dsl) -> Dsl {
        match a {
            BaseValue(a) => match &self.values[a].0 {
                Uneval => BaseValue(0),
                RValue(v) => BaseValue(*v),
                _=>RUndo(Box::new(BaseValue(a)))
            }
            a=>RUndo(Box::new(a))
        }
    }
    pub fn switch_short(&self,ch:&Dsl) -> SwitchShortResult {
        match ch {
            Lside(_) => SwitchLeft,
            Rside(_) => SwitchRight,
            BaseValue(v) => match &self.values[*v].0 {
                Uneval => Die,
                LValue(_) => SwitchLeft,
                RValue(_) => SwitchRight,
                _=>panic!()
            }
            _=>Undecided
        }
    }
    pub fn get_switch(&self,ch:Dsl,a:Dsl,b:Dsl) -> Dsl {
        match self.switch_short(&ch) {
            Die => BaseValue(0),
            SwitchLeft => a,
            SwitchRight => b,
            Undecided => {
                if let BaseValue(x) = a {
                    if x==0 {return b}
                }
                if let BaseValue(x) = b {
                    if x==0 {return a}
                }
                SwitchValue(Box::new(ch),Box::new(a),Box::new(b))
            }
        }
    }
    pub fn create_bool_defn(&mut self) -> (usize,usize,usize) {//true, false, boolean
        (
            self.get_r(1),
            self.get_l(1),
            self.get_lr_type(self.get_unit_type(),self.get_unit_type())
        )
    }
    pub fn get_eq(&mut self,a:Dsl,b:Dsl) -> Dsl {
        match (a,b) {
            (BaseValue(a),BaseValue(b)) => BaseValue(if a==b {
                self.create_bool_defn().0
            } else {
                self.create_bool_defn().1
            }),
            (a,b) => EqProg(Box::new(a),Box::new(b))
        }
    }
    pub fn get_neq(&mut self,a:Dsl,b:Dsl) -> Dsl {
        match (a,b) {
            (BaseValue(a),BaseValue(b)) => BaseValue(if a!=b {
                self.create_bool_defn().0
            } else {
                self.create_bool_defn().1
            }),
            (a,b) => NeqProg(Box::new(a),Box::new(b))
        }
    }
    pub fn substitute(&mut self,a:&Dsl,amt:usize,lim:usize,mut sub:Rc<Vec<(Vec<Dsl>,usize)>>) -> Dsl {
        match a {
            RecursivePlaceholder=>RecursivePlaceholder,
            AccessStack(mut i)=>{
                if i>=lim {i+=amt}
                for (ind,(l,a)) in sub.iter().enumerate() {
                    let a=*a;
                    if i>=a {
                        if i>=a+l.len() {
                            i-=l.len()
                        } else {
                            if ind < sub.len()-1 {
                                let ss = Rc::make_mut(&mut sub);
                                let sv = ss.drain(ind+1..).collect();
                                return self.substitute(&ss[ind].0[i-a],a,0,Rc::new(sv));
                            } else if a>0 {
                                return Self::bump(&l[i-a],a,0)
                            } else {
                                return match Rc::get_mut(&mut sub) {
                                    None=>sub[ind].0[i-a].clone(),
                                    Some(x)=>x.swap_remove(ind).0.swap_remove(i-a)
                                }
                            }
                        }
                    }
                }; AccessStack(i)
            }
            TransferStack(a,b)=>{
                for (_,m) in Rc::make_mut(&mut sub) {*m+=b}
                let whatev = self.substitute(a,amt,lim+b,sub);
                self.get_transferstack(whatev,*b)
            }
            ApplyStack(a,l)=>{
                let lp=l.iter().map(|x|self.substitute(x,amt,lim,sub.clone())).collect();
                let we = self.substitute(a,amt,lim,sub);
                self.get_applied(we,lp)
            }
            BaseValue(a)=>BaseValue(*a),
            Lside(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_l_prog(w)
            }
            Rside(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_r_prog(w)
            }
            Pair(a,b)=>{
                let u = self.substitute(a,amt,lim,sub.clone());
                let v = self.substitute(b,amt,lim,sub);
                self.get_pair_prog(u,v)
            }
            SwitchValue(c,a,b)=>{
                let u = self.substitute(c,amt,lim,sub.clone());
                match self.switch_short(&u) {
                    Die => BaseValue(0),
                    Undecided=>{
                        let v = self.substitute(a,amt,lim,sub.clone());
                        let w = self.substitute(b,amt,lim,sub);
                        if let BaseValue(x) = v {
                            if x==0 {return w}
                        }
                        if let BaseValue(x) = w {
                            if x==0 {return v}
                        }
                        SwitchValue(Box::new(u),Box::new(v),Box::new(w))
                    }
                    SwitchLeft=>self.substitute(a,amt,lim,sub),
                    SwitchRight=>self.substitute(b,amt,lim,sub)
                }
            }
            LUndo(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_undo_left(w)
            }
            RUndo(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_undo_right(w)
            }
            LeftValue(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_left_value(w)
            }
            RightValue(a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_right_value(w)
            }
            EqProg(a,b)=>{
                let u = self.substitute(a,amt,lim,sub.clone());
                let v = self.substitute(b,amt,lim,sub);
                self.get_eq(u,v)
            }
            NeqProg(a,b)=>{
                let u = self.substitute(a,amt,lim,sub.clone());
                let v = self.substitute(b,amt,lim,sub);
                self.get_neq(u,v)
            }
        }
    }
    pub fn bbump(a:&Box<Dsl>,amt:usize,lim:usize) -> Box<Dsl> {Box::new(Self::bump(&(*a),amt,lim))}
    pub fn bump(a:&Dsl,amt:usize,lim:usize) -> Dsl {
        match a {
            RecursivePlaceholder=>RecursivePlaceholder,
            AccessStack(i)=>AccessStack(if *i>=lim {i+amt} else {*i}),
            TransferStack(a,b)=>TransferStack(Self::bbump(a,amt,lim+b),*b),
            ApplyStack(a,b)=>ApplyStack(Self::bbump(a,amt,lim),b.into_iter().map(|x|Self::bump(x,amt,lim)).collect()),
            BaseValue(a)=>BaseValue(*a),
            Lside(a)=>Lside(Self::bbump(a,amt,lim)),
            Rside(a)=>Rside(Self::bbump(a,amt,lim)),
            Pair(a,b)=>Pair(Self::bbump(a,amt,lim),Self::bbump(b,amt,lim)),
            SwitchValue(a,b,c)=>SwitchValue(Self::bbump(a,amt,lim),Self::bbump(b,amt,lim),Self::bbump(c,amt,lim)),
            LUndo(a)=>LUndo(Self::bbump(a,amt,lim)),
            RUndo(a)=>RUndo(Self::bbump(a,amt,lim)),
            LeftValue(a)=>LeftValue(Self::bbump(a,amt,lim)),
            RightValue(a)=>RightValue(Self::bbump(a,amt,lim)),
            NeqProg(a,b)=>NeqProg(Self::bbump(a,amt,lim),Self::bbump(b,amt,lim)),
            EqProg(a,b)=>EqProg(Self::bbump(a,amt,lim),Self::bbump(b,amt,lim))
        }
    }
}





#[derive(Clone)]
pub struct ExpressionContext {
    pub exprs:HashMap<String,(Dsl,usize,usize)>,
}
struct FileInterpreter {
    expr:ExpressionBuilder,
    basepath:PathBuf,
    types:HashMap<String,usize>,
    functions:HashMap<String,(Dsl,usize)>,
    nullary_constr:HashMap<String,ProcPattern>,
    unary_constr:HashMap<String,Vec<bool>>
}
pub fn interpret_file(fullpath:PathBuf) -> (ExpressionBuilder,SpecVariant,(usize,usize)) {
    let contents = read_to_string(fullpath.clone()).expect("Something went wrong reading the file");
    println!("loading: {}",fullpath.display());
    let parsed = spec_parser(contents.as_str()).expect("Parsing failed, so there's an issue").1;
    let mut fi = FileInterpreter {
        expr:ExpressionBuilder::new(),
        basepath:fullpath.parent().unwrap().to_path_buf(),
        types:HashMap::new(),
        functions:HashMap::new(),
        nullary_constr:HashMap::new(),
        unary_constr:HashMap::new()
    };
    for line in parsed.earlier_lines {fi.process_line(line);}
    fi.purge();
    let ty = fi.process_type(parsed.synth_type);
    let (argtype,restype) = uncurry(&mut fi.expr,ty);
    let sp = match parsed.spec_type {
        IOSpec(l)=>{
            let mut s = Spec::new();
            for (args,res) in l {
                let context = Rc::new(ExpressionContext{exprs:HashMap::new()});
                let (args,argstype) = fi.process_program(context.clone(),TupleProg(args));
                let (res,rtype) = fi.process_program(context,res);
                let args = match args {
                    BaseValue(v)=>v,_=>panic!("only basic values allowed as IO examples.")
                };
                let res = match res {
                    BaseValue(v)=>v,_=>panic!("only basic values allowed as IO examples.")
                };
                if argstype != argtype {panic!("argument has incompatible type")}
                if rtype != restype {panic!("example has incompatible type")}
                s.refine(args,EqLit(res));
            }
            JustIO(s)
        },
        LogicalSpec(f)=>{
            let ty = fi.expr.create_bool_defn().2;
            let inner = fi.expr.get_arrow_type(restype,ty);
            let destype = fi.expr.get_arrow_type(argtype,inner);
            let (av,at) = fi.process_function(f);
            if destype != at {panic!("logical function has incompatible type")}
            ConfirmWithFunc(Spec::new(),av)
        },
        RefSpec(f)=>{
            let av = fi.process_uncurried_function(f,ty,argtype);
            ReferenceImpl(av)
        }
    };
    (fi.expr,sp,(argtype,restype))
}
fn to_uncurry_frags(expr:&mut ExpressionBuilder,mut a:usize) -> (Vec<usize>,usize) {
    let mut args : Vec<usize> = Vec::new();
    let res = loop {
        match &expr.types[a] {
            ProcType::ArrowType(c,b)=>{
                args.push(*c);
                a=*b;
            }
            _=>{break a;}
        }
    };
    (args,res)
}
fn uncurry(expr:&mut ExpressionBuilder,a:usize) -> (usize,usize) {
    let (args,res) = to_uncurry_frags(expr,a);
    let mut aar = None;
    for a in args.into_iter().rev() {
        match aar {
            None=>{aar=Some(a)}
            Some(b)=>(aar=Some(expr.get_pair_type(a,b)))
        }
    }
    (aar.expect("given synthesis type isn't a function"),res)
}
impl FileInterpreter {
    fn purge(&self) {
        for (k,v) in self.types.iter() {
            if let Placeholder = &self.expr.types[*v] {
                panic!("Type name not found: {}",k);
            }
        }
    }
    fn process_line(&mut self,line:Line) {
        match line {
            IncludeLine(filename)=>{
                let contents = read_to_string(self.basepath.join(filename)).expect("Something went wrong reading the file");
                for line in decls_parser(contents.as_str()).expect("Parsing failed, so there's an issue").1 {
                    self.process_line(line);
                }
            }
            TypeLine(name,constructors) => {
                let cln = constructors.len();
                if cln==0 {panic!()}
                let mut obby : Option<usize> = None;
                let mut cstrnames : Option<Constname> = None;
                let mut interim = Vec::new();
                for (i,(cstr,l)) in constructors.into_iter().enumerate().rev() {
                    let isl = l.is_some();
                    let (bb,cpath) = match l {
                        None=>{
                            let calc = (0..cln-1).rev().fold(1,|b,x|if i>x {self.expr.get_r(b)} else if i==x {self.expr.get_l(b)} else {b});
                            if cstr=="False" {
                                if let Some(k) = self.expr.falseval {
                                    if k != calc {panic!("Equality operators have been used before definition of boolean types, AND those boolean types betray convention. (make False come before True or define bools earlier).")}
                                }
                                self.expr.falseval=Some(calc)
                            }
                            if cstr=="True" {
                                if let Some(k) = self.expr.trueval {
                                    if k != calc {panic!("Equality operators have been used before definition of boolean types, AND those boolean types betray convention. (make False come before True or define bools earlier).")}
                                }
                                self.expr.trueval=Some(calc)
                            }
                            self.nullary_constr.insert(cstr.to_string(),(0..cln-1).rev().fold(Unit,|b,x|if i>x {RPat(Box::new(b))} else if i==x {LPat(Box::new(b))} else {b}));
                            (//1 is the unit value
                                self.expr.get_unit_type(),
                                BaseValue(calc)
                            )
                        },
                        Some(x)=>{
                            self.unary_constr.insert(cstr.to_string(),(0..cln-1).rev().filter_map(|x|if i>x {Some(true)} else if i==x {Some(false)} else {None}).collect());
                            (
                                self.process_type(x),
                                TransferStack(Box::new((0..cln-1).rev().fold(AccessStack(0),|b,x|if i>x {Rside(Box::new(b))} else if i==x {Lside(Box::new(b))} else {b})),1)
                            )
                        }
                    };
                    interim.push((cstr.to_string(),cpath,if isl {Some(bb)} else {None}));
                    match obby {
                        None => {obby = Some(bb);}
                        Some(x) => {
                            let mut ttt = false;
                            if i==0 {
                                if let Some(y) = self.types.get(name) {
                                    if let Placeholder = &self.expr.types[*y] {
                                        ttt=true;
                                        self.expr.place_lr_type_in_placeholder(bb,x,*y);
                                        obby = Some(*y);
                                    }
                                }
                            }
                            if !ttt {obby = Some(self.expr.get_lr_type(bb,x));}
                        }
                    }
                    match cstrnames {
                        None => {cstrnames=Some(if isl
                            {UnaryName(String::from(cstr))} else
                            {NullaryName(String::from(cstr))}
                        );}
                        Some(x) => {
                            cstrnames=Some(LRSplit(Box::new(if isl
                                {UnaryName(String::from(cstr))} else
                                {NullaryName(String::from(cstr))}),
                            Box::new(x)));
                        }
                    }
                }
                for (a,b,c) in interim {
                    let ntype = match c {
                        Some(c) => self.expr.get_arrow_type(c,obby.unwrap()),
                        None => obby.unwrap()
                    };
                    self.functions.insert(a,(b,ntype));
                }
                self.expr.debug_constr_names.insert(obby.unwrap(),cstrnames.unwrap());
                self.types.insert(name.to_string(),obby.unwrap());
                self.expr.debug_type_names.insert(obby.unwrap(),name.to_string());
            }
            LetLine(name,program) => {
                let (vv,at) = self.process_function(program);
                self.functions.insert(name.to_string(),(BaseValue(vv),at));
            }
        }
    }

    fn process_uncurried_function(&mut self,mut program:Program,curried_type:usize,uncurried:usize) -> usize {
        let (args,resultant) = to_uncurry_frags(&mut self.expr,curried_type);
        let x = args.len();
        let mut context = ExpressionContext{exprs:HashMap::new()};
        match program {
            FixpointProg(innername,innertype,prog) => {
                let ty = self.process_type(innertype);
                if ty != curried_type {panic!("type doesn't match synthesis type")}
                program = *prog;
                let mut pregadget = None;
                for y in (0..x).rev() {
                    let a = AccessStack(y);
                    match pregadget {
                        None=>{pregadget=Some(a);}
                        Some(b)=>{pregadget=Some(Pair(Box::new(a),Box::new(b)));}
                    }
                }
                let fplc = self.expr.get_function_placeholder();
                let gadget = self.expr.get_transferstack(ApplyStack(
                    Box::new(BaseValue(fplc)),vec![pregadget.unwrap()]
                ),1);
                context.exprs.insert(innername.to_string(),(gadget,ty,0));
            }
            _=>{}
        }
        let mut i = 0;
        loop {
            match program {
                FunProg(arg,argtype,inner)=>{
                    let nty = self.process_type(argtype);
                    if nty != args[i] {panic!("type doesn't match synthesis type")}
                    let thaf = (0..x-1).rev().fold(
                        AccessStack(0),
                        |b,x|if i>x {RUndo(Box::new(b))} else if i==x {LUndo(Box::new(b))} else {b}
                    );
                    i+=1;
                    context.exprs.insert(arg.to_string(),(thaf,nty,0));
                    program = *inner;
                }
                _=>{break;}
            }
        }
        let (mut av,mut at) = self.process_program(Rc::new(context),program);
        if i<x {
            av=ApplyStack(Box::new(av),
                (i..x).map(|i|{
                    match &self.expr.types[at] {
                        ProcType::ArrowType(a,b)=>{
                            if *a != args[i] {panic!("type doesn't match synthesis type")}
                            at=*b;
                        }
                        _=>panic!("type doesn't match synthesis type")
                    }
                    (0..x-1).rev().fold(
                        AccessStack(0),
                        |b,x|if i>x {self.expr.get_r_prog(b)} else if i==x {self.expr.get_l_prog(b)} else {b}
                    )
                }).collect()
            );
        }
        if at != resultant {
            panic!("type doesn't match synthesis type")
        }
        let av = self.expr.get_transferstack(av,1);
        self.expr.insert_function(av,vec![uncurried],resultant)
    }

    fn process_function(&mut self,mut program:Program) -> (usize,usize) {
        let mut context = ExpressionContext{exprs:HashMap::new()};
        let mut reqtype = None;
        match program {
            FixpointProg(innername,innertype,prog) => {
                let ty = self.process_type(innertype);
                program = *prog;
                reqtype = Some(ty);
                context.exprs.insert(innername.to_string(),(BaseValue(self.expr.get_function_placeholder()),ty,0));
            }
            _=>{}
        }
        let (av,at) = self.process_program(Rc::new(context),program);
        if let Some(k) = reqtype {
            if k != at {panic!("fixpoint type conflict")}
        }
        let (argtype,restype) = to_uncurry_frags(&mut self.expr,at);
        let vv = self.expr.insert_function(av,argtype,restype);
        (vv,at)
    }
    fn process_type(&mut self,t:Type) -> usize {
        match t {
            IdentType(name) => match self.types.get(name) {
                Some(x)=>*x,
                None=>{
                    let a = self.expr.get_placeholder_type();
                    self.types.insert(name.to_string(),a);
                    a
                }
            }.clone(),
            StarType(a,b) => {
                let at = self.process_type(*a);
                let bt = self.process_type(*b);
                self.expr.get_pair_type(at,bt)
            }
            Type::ArrowType(a,b) => {
                let at = self.process_type(*a);
                let bt = self.process_type(*b);
                self.expr.get_arrow_type(at,bt)
            }
        }
    }
    fn process_pattern(&self,x:Value) -> ProcPattern {
        match x {
            NumericValue(amt) => {
                let mut base = LPat(Box::new(Unit));
                for _ in 0..amt {base = RPat(Box::new(base));} base
            }
            IdentValue(name) => {
                if let Some(x) = self.nullary_constr.get(name) {return x.clone()}
                if let Some(_) = self.unary_constr.get(name) {panic!("that constructor takes arguments");}
                VarPat(name.to_string())
            },
            AppValue(mut l) => {
                let name = match l.remove(0) {
                    IdentValue(k)=>k,
                    _=>panic!("not a valid constructor")
                };
                let param = if l.len()==1 {
                    self.process_pattern(l.remove(0))
                } else {
                    self.process_pattern(AppValue(l))
                };
                if let Some(x) = self.unary_constr.get(name) {
                    return x.iter().fold(param,|b,x|if *x {RPat(Box::new(b))} else {LPat(Box::new(b))})
                }
                if let Some(x) = self.nullary_constr.get(name) {//gotta tolerate this even though it's wrong
                    return x.clone();
                }
                panic!("constructor name not found")
            }
            TupleValue(l) => {
                let mut obby : Option<ProcPattern> = None;
                for sub in l.into_iter().rev() {
                    let pat = self.process_pattern(sub);
                    match obby {
                        None => {obby = Some(pat);}
                        Some(p) => {obby = Some(PairPat(Box::new(pat),Box::new(p)));}
                    }
                }
                obby.unwrap()
            }
        }
    }
    fn process_program(&mut self,mut expr:Rc<ExpressionContext>,x:Program) -> (Dsl,usize) {
        match x {
            FixpointProg(..) => panic!("fixpoint in strange position..."),
            FunProg(arg,argtype,inner) => {
                let nty = self.process_type(argtype);
                let mtr = Rc::make_mut(&mut expr);
                for (_,_,a) in mtr.exprs.values_mut() {*a+=1;}
                mtr.exprs.insert(arg.to_string(),(AccessStack(0),nty,0));
                let (rr,t) = self.process_program(expr,*inner);
                (self.expr.get_transferstack(rr,1),self.expr.get_arrow_type(nty,t))
            }
            AppProg(mut l) => {
                let (wv,mut wt) = self.process_program(expr.clone(),l.remove(0));
                let (lv,lt) : (Vec<_>,Vec<_>) = l.into_iter().map(|x|self.process_program(expr.clone(),x)).unzip();
                let glgl = wt;
                for (i,t) in lt.into_iter().enumerate() {
                    match &self.expr.types[wt] {
                        ProcType::ArrowType(a,b) => {
                            if *a != t {
                                println!("\nfunction type: {:#?}\n",DebugType{t:glgl,expr:&self.expr,depth:5});
                                println!("\nexpected: {:#?}\nrecieved: {:#?}\n",DebugType{t:*a,expr:&self.expr,depth:5},DebugType{t:t,expr:&self.expr,depth:5});
                                panic!("invalid type for argument: {:#?}, all args: {:#?}",lv[i],lv)
                            }
                            wt=*b;
                        }
                        _=>panic!("arguments applied to non-function")
                    }
                }
                (self.expr.get_applied(wv,lv),wt)
            }
            NumericProg(amt) => {
                let mut base = self.expr.get_l(self.expr.get_unit_value());
                for _ in 0..amt {base = self.expr.get_r(base);}
                (BaseValue(base),self.types.get("nat").expect("Integer notation not supported here").clone())
            }
            TupleProg(l) => {
                let mut obby : Option<(Dsl,usize)> = None;
                for sub in l.into_iter().rev() {
                    let (av,at) = self.process_program(expr.clone(),sub);
                    match obby {
                        None => {obby = Some((av,at));}
                        Some((bv,bt)) => {obby = Some((self.expr.get_pair_prog(av,bv),self.expr.get_pair_type(at,bt)));}
                    }
                }
                obby.unwrap()
            }
            IdentProg(name) => {
                if let Some((v,t,shift)) = expr.exprs.get(name) {
                    if *shift==0 {return (v.clone(),*t)}
                    return (ExpressionBuilder::bump(v,*shift,0),*t)
                }
                if let Some(r) = self.functions.get(name) {return r.clone()}
                panic!("no such symbol: {}",name)
            }
            AccProg(a,u) => {
                let (mut wv,mut wt) = self.process_program(expr,*a);
                for _ in 0..u {
                    match &self.expr.types[wt] {
                        PairType(_,b) => {
                            wt=*b;
                            wv = RightValue(Box::new(wv));
                        }
                        _=>panic!("arguments applied to non-function")
                    }
                }
                match &self.expr.types[wt] {
                    PairType(a,_) => {
                        wv=LeftValue(Box::new(wv));
                        wt=*a;
                    }
                    _=>{}
                }
                (wv,wt)
            }
            ComparisonProg(a,b)=>{
                let (av,at) = self.process_program(expr.clone(),*a);
                let (bv,bt) = self.process_program(expr,*b);
                if at != bt {panic!("cannot compare values of different types")}
                (self.expr.get_eq(av,bv),self.expr.create_bool_defn().2)
            }
            NegComparisonProg(a,b)=>{
                let (av,at) = self.process_program(expr.clone(),*a);
                let (bv,bt) = self.process_program(expr,*b);
                if at != bt {panic!("cannot compare values of different types")}
                (self.expr.get_neq(av,bv),self.expr.create_bool_defn().2)
            }
            MatchProg(a,l) => {
                let (pats,mut progs) : (Vec<_>,Vec<_>) = l.into_iter().map(|(v,p)|(self.process_pattern(v),NotFinished(Some(p)))).unzip();
                fn inner<'a>(
                    s:&'a mut FileInterpreter,
                    mut queue:Vec<(Vec<(usize,&'a ProcPattern)>,HashMap<usize,(&'a String,usize)>,Dsl,usize)>,
                    mut splitcandidates:Vec<(Vec<(usize,&'a ProcPattern)>,Vec<(usize,&'a ProcPattern)>,HashMap<usize,(&'a String,usize)>,bool,Dsl,usize)>,
                    mut currentmin:Option<usize>,
                    mut stagnant:Vec<(Vec<(usize,&'a ProcPattern)>,HashMap<usize,(&'a String,usize)>,Dsl,usize)>,
                    allprogs:Vec<usize>,
                    commontype:&mut Option<usize>,
                    mut expr:Rc<ExpressionContext>,
                    availableprogs:&mut Vec<FinishedOrNot>
                ) -> Dsl {
                    while let Some((red,mut backvars,path,btype)) = queue.pop() {
                        if red.len()==0 {stagnant.push((red,backvars,path,btype));continue;}
                        match red[0].1 {
                            PairPat(..)=>{
                                let (l,r) : (Vec<_>,Vec<_>) = red.into_iter().filter_map(|(i,x)|match x{
                                    PairPat(a,b)=>Some(((i,&**a),(i,&**b))),
                                    VarPat(e)=>{backvars.insert(i,(e,btype));None}
                                    _=>panic!("strange branch mismatch...")
                                }).unzip();
                                let (ltype,rtype) = match s.expr.types[btype] {
                                    PairType(a,b)=>(a,b),
                                    _=>panic!("doesn't fit type...")
                                };
                                queue.push((l,backvars.clone(),LeftValue(Box::new(path.clone())),ltype));
                                queue.push((r,backvars,RightValue(Box::new(path)),rtype));
                            }
                            LPat(_)|RPat(_) => {
                                let whwh = if let LPat(_) = red[0].1 {true} else {false};
                                let mut l : Vec<(usize,&ProcPattern)> = Vec::new();
                                let mut r : Vec<(usize,&ProcPattern)> = Vec::new();
                                for (i,x) in red {
                                    match x {
                                        LPat(x)=>{l.push((i,&*x))}
                                        RPat(x)=>{r.push((i,&*x))}
                                        VarPat(e)=>{backvars.insert(i,(e,btype));}
                                        _=>panic!("strange branch mismatch...")
                                    }
                                }
                                if let Some(x)=currentmin {
                                    if l.len()+r.len()>=splitcandidates[x].0.len()+splitcandidates[x].1.len() {
                                        currentmin=Some(splitcandidates.len());
                                    }
                                } else {
                                    currentmin=Some(splitcandidates.len());
                                }
                                splitcandidates.push((l,r,backvars,whwh,path,btype));
                            }
                            VarPat(..)=>{stagnant.push((red,backvars,path,btype))}
                            Unit=>{}
                        }
                    }
                    if let Some(schbooey) = currentmin {
                        let (lside,rside,backvars,firstelem,path,btype) = splitcandidates.swap_remove(schbooey);
                        let forbid_left : HashSet<usize> = rside.iter().map(|(a,_)|*a).collect();
                        let forbid_right : HashSet<usize> = lside.iter().map(|(a,_)|*a).collect();
                        let mut queue_a : Vec<_> = stagnant.iter().cloned().map(|(mut x,s,w,j)|{
                            x.retain(|(x,_)|!forbid_left.contains(x));
                            (x,s,w,j)
                        }).collect();
                        let mut queue_b : Vec<_> = stagnant.into_iter().map(|(mut x,s,w,j)|{
                            x.retain(|(x,_)|!forbid_right.contains(x));
                            (x,s,w,j)
                        }).collect();
                        let splitcandidates_a : Vec<_> = splitcandidates.iter().cloned().map(|(mut x,mut y,s,u,w,j)|{
                            x.retain(|(x,_)|!forbid_left.contains(x));
                            y.retain(|(x,_)|!forbid_left.contains(x));
                            (x,y,s,u,w,j)
                        }).collect();
                        let amax = splitcandidates_a.iter().enumerate().max_by_key(|&(_,(x,y,_,_,_,_))|x.len()+y.len()).map(|(i,_)|i);
                        let splitcandidates_b : Vec<_> = splitcandidates.into_iter().map(|(mut x,mut y,s,u,w,j)|{
                            x.retain(|(x,_)|!forbid_right.contains(x));
                            y.retain(|(x,_)|!forbid_right.contains(x));
                            (x,y,s,u,w,j)
                        }).collect();
                        let bmax = splitcandidates_b.iter().enumerate().max_by_key(|&(_,(x,y,_,_,_,_))|x.len()+y.len()).map(|(i,_)|i);
                        let (ltype,rtype) = match s.expr.types[btype] {
                            LRType(a,b)=>(a,b),
                            _=>panic!("doesn't fit type...")
                        };
                        let mut leftfilt = allprogs.clone();
                        leftfilt.retain(|x|!forbid_left.contains(x));
                        let mut rightfilt = allprogs;
                        rightfilt.retain(|x|!forbid_right.contains(x));
                        if firstelem {
                            queue_b.push((rside,backvars.clone(),RUndo(Box::new(path.clone())),rtype));
                            let lbranch = inner(s,vec![(lside,backvars,LUndo(Box::new(path.clone())),ltype)],splitcandidates_a,amax,queue_a,leftfilt,commontype,expr.clone(),availableprogs);
                            let rbranch = inner(s,queue_b,splitcandidates_b,bmax,vec![],rightfilt,commontype,expr,availableprogs);
                            s.expr.get_switch(path,lbranch,rbranch)
                        } else {
                            queue_a.push((lside,backvars.clone(),LUndo(Box::new(path.clone())),ltype));
                            let lbranch = inner(s,queue_a,splitcandidates_a,amax,vec![],leftfilt,commontype,expr.clone(),availableprogs);
                            let rbranch = inner(s,vec![(rside,backvars,RUndo(Box::new(path.clone())),rtype)],splitcandidates_b,bmax,queue_b,rightfilt,commontype,expr,availableprogs);
                            s.expr.get_switch(path,lbranch,rbranch)
                        }
                    } else {
                        if allprogs.len()==0 {return BaseValue(0);}
                        let fp = allprogs[0];
                        match &mut availableprogs[fp] {
                            Finished(x)=>x.clone(),
                            NotFinished(p)=>{
                                for (awk,bckv,v,t) in stagnant {
                                    let (name,ty) = match bckv.get(&fp) {
                                        None=>(match awk[0].1 {VarPat(n)=>n,_=>panic!()},t),
                                        Some(x)=>*x
                                    };
                                    let mtr = Rc::make_mut(&mut expr);
                                    mtr.exprs.insert(name.clone(),(v,ty,0));
                                }
                                let pp = take(p).unwrap();
                                let (av,at) = s.process_program(expr,pp);
                                availableprogs[allprogs[0]]=Finished(av.clone());
                                match commontype {
                                    Some(c) => {
                                        if *c != at {panic!("mismatched arm types")}
                                    }
                                    None => {*commontype=Some(at)}
                                }
                                av
                            }
                        }
                    }
                }
                let (av,at) = self.process_program(expr.clone(),*a);
                let mut commontype = None;
                let val = inner(
                    self,
                    vec![(pats.iter().enumerate().collect(),HashMap::new(),av,at)],
                    vec![],None,vec![],(0..progs.len()).collect(),&mut commontype,expr,&mut progs
                );
                (val,commontype.unwrap())
            }
        }
    }
}
enum FinishedOrNot<'a> {
    Finished(Dsl),
    NotFinished(Option<Program<'a>>)
}
use FinishedOrNot::{*};















