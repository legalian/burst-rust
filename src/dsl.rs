

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




#[derive(Clone,Debug)]
pub enum ProcPattern {
    CPat(usize,Vec<ProcPattern>),
    VarPat(usize,String)
}
use ProcPattern::{*};

#[derive(Clone,PartialEq,Eq)]
pub enum Dsl {
    RecursivePlaceholder,

    TransferStack(Box<Dsl>,usize),
    AccessStack(usize),
    ApplyStack(Box<Dsl>,Vec<Dsl>),

    Deconstruct(usize,usize,Box<Dsl>),
    Construct(usize,Vec<Dsl>),
    BaseValue(usize),
    SwitchValue(Box<Dsl>,Vec<Dsl>),

    EqProg(Box<Dsl>,Box<Dsl>),
    NeqProg(Box<Dsl>,Box<Dsl>)
}
use Dsl::{*};


impl ExpressionBuilder {
    pub fn get_transferstack(&mut self,a:Dsl,b:usize) -> Dsl {//this attempts eta-reduction, helpful to the algorithm because of the function caches
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
    pub fn get_deconstructor(&mut self,x:usize,y:usize,a:Dsl) -> Dsl {
        match a {
            Construct(a,mut b) if a==x => b.remove(y),
            BaseValue(a) => match &self.values[a].0 {
                Uneval => BaseValue(0),
                Const(j,i) if *j==x => BaseValue(i[y]),
                _=>Deconstruct(x,y,Box::new(BaseValue(a)))
            }
            a=>Deconstruct(x,y,Box::new(a))
        }
    }
    pub fn get_tuple_prog(&mut self,b:Vec<Dsl>,types:Vec<usize>) -> (usize,usize,Dsl) {
        let (t,a) = self.get_tuple_type(types);
        if b.iter().all(|x|if let BaseValue(_)=x {true} else {false}) {
            return (t,a,BaseValue(self.get_constructed(a,b.into_iter().map(|x|if let BaseValue(x)=x {x} else {panic!()}).collect())))
        }
        (t,a,Construct(a,b))
    }
    pub fn get_construct_prog(&mut self,a:usize,b:Vec<Dsl>) -> Dsl {
        if b.iter().all(|x|if let BaseValue(_)=x {true} else {false}) {
            return BaseValue(self.get_constructed(a,b.into_iter().map(|x|if let BaseValue(x)=x {x} else {panic!()}).collect()))
        }
        Construct(a,b)
    }
    pub fn switch_short(&self,ch:&Dsl) -> Option<Option<usize>> {
        match ch {
            Construct(y,_) => Some(Some(self.constructors[*y].index)),
            BaseValue(v) => match &self.values[*v].0 {
                Uneval=> Some(None),
                Const(y,_) => Some(Some(self.constructors[*y].index)),
                _=>None
            }
            _=>None
        }
    }
    pub fn get_switch(&self,ch:Dsl,mut a:Vec<Dsl>) -> Dsl {
        match self.switch_short(&ch) {
            Some(None) => BaseValue(0),
            Some(Some(x)) => a.remove(x),
            None => {
                let mut nocount = 0;
                let mut j = 0;
                for (i,b) in a.iter().enumerate() {
                    if let BaseValue(x) = b {
                        if *x==0 {
                            nocount+=1;
                            j=i;
                        }
                    }
                }
                if nocount==0 {return BaseValue(0)}
                if nocount==1 {return a.remove(j)}
                SwitchValue(Box::new(ch),a)
            }
        }
    }
    pub fn get_eq(&mut self,a:Dsl,b:Dsl) -> Dsl {
        let bb = self.force_get_bool();
        let falsetrue = self.get_constructors_for(bb);
        match (a,b) {
            (BaseValue(a),BaseValue(b)) => BaseValue(falsetrue[if a==b {1} else {0}]),
            (a,b) => EqProg(Box::new(a),Box::new(b))
        }
    }
    pub fn get_neq(&mut self,a:Dsl,b:Dsl) -> Dsl {
        let bb = self.force_get_bool();
        let falsetrue = self.get_constructors_for(bb);
        match (a,b) {
            (BaseValue(a),BaseValue(b)) => BaseValue(falsetrue[if a!=b {1} else {0}]),
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
            Construct(x,a)=>{
                let w = a.iter().map(|b|self.substitute(b,amt,lim,sub.clone())).collect();
                self.get_construct_prog(*x,w)
            }
            SwitchValue(c,a)=>{
                let u = self.substitute(c,amt,lim,sub.clone());
                match self.switch_short(&u) {
                    Some(None) => BaseValue(0),
                    None=>{
                        let w = a.iter().map(|b|self.substitute(b,amt,lim,sub.clone())).collect();
                        self.get_switch(u,w)
                    }
                    Some(Some(u))=>self.substitute(&a[u],amt,lim,sub),
                }
            }
            Deconstruct(x,y,a)=>{
                let w = self.substitute(a,amt,lim,sub);
                self.get_deconstructor(*x,*y,w)
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
            Construct(x,b)=>Construct(*x,b.into_iter().map(|x|Self::bump(x,amt,lim)).collect()),
            SwitchValue(a,b)=>SwitchValue(Self::bbump(a,amt,lim),b.into_iter().map(|x|Self::bump(x,amt,lim)).collect()),
            Deconstruct(x,y,a)=>Deconstruct(*x,*y,Self::bbump(a,amt,lim)),
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
    constructors:HashMap<String,usize>
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
        constructors:HashMap::new()
    };
    let mut pel = parsed.earlier_lines;
    fi.early_process_bools_and_nats(&mut pel);
    for line in pel {fi.process_line(line);}
    fi.purge();
    let ty = fi.process_type(parsed.synth_type);
    let (argtype,restype) = uncurry(&mut fi.expr,ty);
    let sp = match parsed.spec_type {
        IOSpec(l)=>{
            let mut s = Spec::new();
            for (mut args,res) in l {
                let context = Rc::new(ExpressionContext{exprs:HashMap::new()});
                let (args,argstype) = fi.process_program(context.clone(),if args.len()==1 {args.remove(0)} else {TupleProg(args)});
                let (res,rtype) = fi.process_program(context,res);
                let args = match args {
                    BaseValue(v)=>v,_=>panic!("only basic values allowed as IO examples.")
                };
                let res = match res {
                    BaseValue(v)=>v,_=>panic!("only basic values allowed as IO examples.")
                };
                if argstype != argtype {panic!("argument has incompatible type. Expected: {:?} Got: {:?}",DebugType{t:argtype,expr:&fi.expr,depth:55},DebugType{t:argstype,expr:&fi.expr,depth:55})}
                if rtype != restype {panic!("example has incompatible type. Expected: {:?} Got: {:?}",DebugType{t:restype,expr:&fi.expr,depth:55},DebugType{t:rtype,expr:&fi.expr,depth:55})}
                s.refine(args,EqLit(res));
            }
            JustIO(s)
        },
        LogicalSpec(..)=>{
            panic!()
            // let ty = fi.expr.create_bool_defn().2;
            // let inner = fi.expr.get_arrow_type(restype,ty);
            // let destype = fi.expr.get_arrow_type(argtype,inner);
            // let (av,at) = fi.process_function(f);
            // if destype != at {panic!("logical function has incompatible type")}
            // ConfirmWithFunc(Spec::new(),av)
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
    let (mut args,res) = to_uncurry_frags(expr,a);
    if args.len()==0 {panic!("given synthesis type isn't a function")}
    let aar = if args.len()==1 {args.remove(0)} else {expr.get_tuple_type(args).0};
    (aar,res)
}
impl FileInterpreter {
    fn purge(&self) {
        for (k,v) in self.types.iter() {
            if let Placeholder = &self.expr.types[*v] {
                panic!("Type name not found: {}",k);
            }
        }
    }
    fn early_process_bools_and_nats(&mut self,line:&mut Vec<Line>) {
        let mut i=0;
        while i<line.len() {
            match &line[i] {
                TypeLine(name,_) if *name=="bool" || *name=="nat" => {
                    self.process_line(line.remove(i))
                }
                _=>{i+=1}
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
                // let mut interim = Vec::new();
                let mut bb : Vec<Vec<usize>> = Vec::new();
                let mut names : Vec<String> = Vec::new();
                for (cst,l) in constructors.into_iter() {
                    bb.push(l.into_iter().map(|x|self.process_type(x)).collect());
                    names.push(String::from(cst));
                }
                let (consts,obby) = if let Some(y) = self.types.get(name) {
                    if let Placeholder = &self.expr.types[*y] {
                        (self.expr.place_type_in_placeholder(*y,bb.clone(),names),*y)
                    } else {panic!("type already defined!")}
                } else {
                    let y = self.expr.get_placeholder_type();
                    self.types.insert(name.to_string(),y);
                    (self.expr.place_type_in_placeholder(y,bb.clone(),names),y)
                };
                if name=="bool" {
                    self.expr.bool_type = Some(obby);
                }
                if name=="nat" {
                    self.expr.nat_type = Some(obby);
                }
                for cstr in consts {
                    let f = &self.expr.constructors[cstr];
                    let fname = f.name.clone().unwrap();
                    if f.argtypes.len()==0 {
                        self.functions.insert(fname,(BaseValue(self.expr.get_constructed(cstr,Vec::new())),obby));
                    } else if f.argtypes.len()==1 {
                        let farg = f.argtypes[0];
                        let ntyp = self.expr.get_arrow_type(farg,obby);
                        let nval = TransferStack(Box::new(Construct(cstr,vec![AccessStack(0)])),1);
                        self.functions.insert(fname,(nval,ntyp));
                    } else {
                        let fclone = f.argtypes.clone();
                        let (ttype,tconst) = self.expr.get_tuple_type(fclone);
                        let ntyp = self.expr.get_arrow_type(ttype,obby);
                        let f = &self.expr.constructors[cstr];
                        let fargs = (0..f.argtypes.len()).map(|w|Deconstruct(tconst,w,Box::new(AccessStack(0)))).collect();
                        let nval = TransferStack(Box::new(Construct(cstr,fargs)),1);
                        self.functions.insert(fname,(nval,ntyp));
                    }
                }
                self.expr.debug_type_names.insert(obby,name.to_string());
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
        let (_,cstrv,deed) = self.expr.get_tuple_prog((0..x).map(|y|AccessStack(y)).collect(),args.clone());
        match program {
            FixpointProg(innername,innertype,prog) => {
                let ty = self.process_type(innertype);
                if ty != curried_type {panic!("type doesn't match synthesis type")}
                program = *prog;
                let fplc = self.expr.get_function_placeholder();
                let gadget = self.expr.get_transferstack(ApplyStack(
                    Box::new(BaseValue(fplc)),vec![deed]
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
                    let thaf = Deconstruct(cstrv,i,Box::new(AccessStack(0)));
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
                    self.expr.get_construct_prog(i,vec![AccessStack(0)])
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
            StarType(b) => {
                let innerp = b.into_iter().map(|z|self.process_type(z)).collect();
                self.expr.get_tuple_type(innerp).0
            }
            Type::ArrowType(a,b) => {
                let at = self.process_type(*a);
                let bt = self.process_type(*b);
                self.expr.get_arrow_type(at,bt)
            }
        }
    }
    fn process_pattern(&mut self,x:Value,t:usize) -> ProcPattern {
        match x {
            NumericValue(amt) => {
                let bb = self.expr.force_get_nat();
                let os = self.expr.get_constructors_for(bb);
                let mut base = CPat(os[0],Vec::new());
                for _ in 0..amt {base = CPat(os[1],vec![base]);} base
            }
            IdentValue(name) => {
                if let Some(x) = self.constructors.get(name) {
                    let f = &self.expr.constructors[*x];
                    if f.argtypes.len()>0 {panic!("that constructor takes arguments!");}
                    return CPat(*x,Vec::new());
                }
                VarPat(t,name.to_string())
            },
            AppValue(mut l) => {
                let name = match l.remove(0) {
                    IdentValue(k)=>k,
                    _=>panic!("not a valid constructor")
                };
                if let Some(x) = self.constructors.get(name) {
                    let x=*x;
                    let f = &self.expr.constructors[x];
                    if f.argtypes.len()>0 {
                        if f.argtypes.len()!=1 {panic!("only nullary constructors are expected from the benchmarks... (but are totally supported under the hood)");}
                        let far = f.argtypes[0];
                        let param = if l.len()==1 {
                            self.process_pattern(l.remove(0),far)
                        } else {
                            self.process_pattern(AppValue(l),far)
                        };
                        CPat(x,vec![param]);
                    } else {
                        return CPat(x,Vec::new());
                    }
                }
                panic!("constructor name not found")
            }
            TupleValue(l) => {
                let cl = self.expr.get_constructors_for(t);
                if cl.len()!=1 {panic!("tuple not expected here!")}
                let f = &self.expr.constructors[cl[0]];
                if f.argtypes.len()!=l.len() {panic!("wrong number of arguments for tuple!");}
                // let (a,b) : (Vec<_>,Vec<_>) = l.into_iter().map(|x|self.process_pattern(x)).unzip();
                // self.expr.get_tuple_type();
                CPat(cl[0],l.into_iter().zip(f.argtypes.clone().into_iter()).map(|(p,t)|self.process_pattern(p,t)).collect())
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
                                println!("{:#?}",self.expr.types);
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
                let bb = self.expr.force_get_nat();
                let os = self.expr.get_constructors_for(bb);
                let mut base = self.expr.get_constructed(os[0],Vec::new());
                for _ in 0..amt {base = self.expr.get_constructed(os[1],vec![base]);}
                (BaseValue(base),bb)
            }
            TupleProg(l) => {
                let (l,lt) : (Vec<_>,Vec<_>) = l.into_iter().map(|x|self.process_program(expr.clone(),x)).unzip();
                let (b,bc) = self.expr.get_tuple_type(lt);
                (self.expr.get_construct_prog(bc,l),b)
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
                let (wv,wt) = self.process_program(expr,*a);
                let cst = self.expr.get_constructors_for(wt);
                if cst.len()!=1 {panic!("cannot unsafely access this value.")}
                let far = self.expr.constructors[cst[0]].argtypes[u];
                let w = self.expr.get_deconstructor(cst[0],u,wv);
                (w,far)
            }
            ComparisonProg(a,b)=>{
                let (av,at) = self.process_program(expr.clone(),*a);
                let (bv,bt) = self.process_program(expr,*b);
                if at != bt {panic!("cannot compare values of different types")}
                (self.expr.get_eq(av,bv),self.expr.force_get_bool())
            }
            NegComparisonProg(a,b)=>{
                let (av,at) = self.process_program(expr.clone(),*a);
                let (bv,bt) = self.process_program(expr,*b);
                if at != bt {panic!("cannot compare values of different types")}
                (self.expr.get_neq(av,bv),self.expr.force_get_bool())
            }
            MatchProg(a,l) => {
                enum FinishedOrNot<'a> {
                    Finished(Dsl),
                    NotFinished(Option<Program<'a>>)
                }
                use FinishedOrNot::{*};
                let (av,at) = self.process_program(expr.clone(),*a);
                let (pats,mut progs) : (Vec<_>,Vec<_>) = l.into_iter().map(|(v,p)|(self.process_pattern(v,at),NotFinished(Some(p)))).unzip();
                fn inner<'a>(
                    s:&'a mut FileInterpreter,
                    mut queue:Vec<(Vec<(usize,&'a ProcPattern)>,HashMap<usize,(&'a String,usize)>,Dsl,usize)>,
                    mut splitcandidates:Vec<(Vec<Vec<Vec<(usize,&'a ProcPattern)>>>,HashMap<usize,(&'a String,usize)>,usize,Dsl,usize)>,
                    mut stagnant:Vec<(Vec<(usize,&'a ProcPattern)>,HashMap<usize,(&'a String,usize)>,Dsl,usize)>,
                    allprogs:Vec<usize>,
                    commontype:&mut Option<usize>,
                    mut expr:Rc<ExpressionContext>,
                    availableprogs:&mut Vec<FinishedOrNot>
                ) -> Dsl {
                    while let Some((red,mut backvars,path,btype)) = queue.pop() {
                        if red.len()==0 {stagnant.push((red,backvars,path,btype));continue;}
                        match red[0].1 {
                            CPat(red_j,_)=>{
                                let whwh = s.expr.constructors[*red_j].index;
                                let types = match &s.expr.types[btype] {
                                    EnumType(b)=>b,
                                    _=>panic!("doesn't fit type...")
                                };
                                let mut dvecs : Vec<Vec<Vec<_>>> = types.iter().map(|u|u.iter().map(|_|Vec::new()).collect()).collect();
                                for (i,x) in red {
                                    match x {
                                        CPat(j,x)=>{
                                            let f = &s.expr.constructors[*j];
                                            if f.restype != btype {panic!("pattern var mismatch");}
                                            for (h,x) in x.iter().enumerate() {
                                                dvecs[f.index][h].push((i,x));
                                            }
                                        }
                                        VarPat(k,e)=>{
                                            if *k != btype {panic!("pattern var mismatch");}
                                            backvars.insert(i,(e,btype));
                                        }
                                    }
                                }
                                if dvecs.len()==1 {
                                    for (i,(d,t)) in dvecs.remove(0).into_iter().zip(types[0].iter()).enumerate() {
                                        queue.push((d,backvars.clone(),Deconstruct(0,i,Box::new(path.clone())),*t));
                                    }
                                } else {
                                    splitcandidates.push((dvecs,backvars,whwh,path,btype));
                                }
                            }
                            VarPat(..)=>{stagnant.push((red,backvars,path,btype))}
                        }
                    }
                    let currentmin = splitcandidates.iter().enumerate().max_by_key(|&(_,(x,_,_,_,_))|x.iter().map(|o|o.len()).sum::<usize>()).map(|(i,_)|i);
                    if let Some(schbooey) = currentmin {
                        let (sides,backvars,firstelem,path,btype) = splitcandidates.swap_remove(schbooey);
                        let forbids : Vec<HashSet<usize>> = (0..sides.len()).map(|ou|(0..sides.len()).filter(|k|*k!=ou).map(|u|sides[u][0].iter().map(|(a,_)|*a)).flatten().collect()).collect();
                        let btypeconst = s.expr.get_constructors_for(btype);
                        let branches : Vec<Dsl> = sides.into_iter().zip(forbids.into_iter()).enumerate().map(|(ou,(thisside,forbid))|{
                            let mut newqueue : Vec<_> = stagnant.iter().cloned().map(|(mut x,s,w,j)|{
                                x.retain(|(x,_)|!forbid.contains(x));
                                (x,s,w,j)
                            }).collect();
                            let newsplit = splitcandidates.iter().cloned().map(|(mut x,s,u,w,j)|{
                                for y in x.iter_mut() {
                                    for z in y.iter_mut() {
                                        z.retain(|(x,_)|!forbid.contains(x));
                                    }
                                }
                                (x,s,u,w,j)
                            }).collect();
                            let subtypes = match &s.expr.types[btype] {
                                EnumType(b)=>&b[ou],
                                _=>panic!("doesn't fit type...")
                            };
                            let filt = allprogs.iter().cloned().filter(|x|!forbid.contains(x)).collect();
                            if ou==firstelem {
                                for (j,(sid,sty)) in thisside.into_iter().zip(subtypes).enumerate() {
                                    newqueue.push((sid,backvars.clone(),Deconstruct(btypeconst[ou],j,Box::new(path.clone())),*sty));
                                }
                                inner(s,newqueue,newsplit,vec![],filt,commontype,expr.clone(),availableprogs)
                            } else {
                                let icd = thisside.into_iter().zip(subtypes).enumerate().map(|(j,(sid,sty))|
                                    (sid,backvars.clone(),Deconstruct(btypeconst[ou],j,Box::new(path.clone())),*sty)
                                ).collect();
                                inner(s,
                                    icd,
                                    newsplit,newqueue,filt,
                                    commontype,expr.clone(),availableprogs
                                )
                            }
                        }).collect();
                        s.expr.get_switch(path,branches)
                    } else {
                        if allprogs.len()==0 {return BaseValue(0);}
                        let fp = allprogs[0];
                        match &mut availableprogs[fp] {
                            Finished(x)=>x.clone(),
                            NotFinished(p)=>{
                                for (awk,bckv,v,t) in stagnant {
                                    let (name,ty) = match bckv.get(&fp) {
                                        None=>(match awk[0].1 {VarPat(_,n)=>n,_=>panic!()},t),
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
                let mut commontype = None;
                let val = inner(
                    self,
                    vec![(pats.iter().enumerate().collect(),HashMap::new(),av,at)],
                    vec![],vec![],(0..progs.len()).collect(),&mut commontype,expr,&mut progs
                );
                (val,commontype.unwrap())
            }
        }
    }
}














