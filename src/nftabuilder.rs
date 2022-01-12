

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::collections::hash_map::Entry::*;
use crate::ntfa::{*};
use crate::spec::{*};
use crate::dsl::{*};
use crate::queue::{*};
use Dsl::{*};

pub enum ProcType {
    PairType(usize,usize),
    LRType(usize,usize),
    ArrowType(usize,usize),
    UnitType,
    Placeholder
}
use ProcType::{*};

pub enum ProcValue {
    PairValue(usize,usize),
    LValue(usize),
    RValue(usize),
    FuncAsValue(usize),
    UnitValue,
    Uneval
}
use ProcValue::{*};


pub struct FunctionEntry {
    dsl:Rc<Dsl>,
    concval:usize,
    argtypes:Vec<usize>,
    restype:usize
}
pub struct ExpressionBuilder {
    functions:Vec<FunctionEntry>,
    functionmemo:HashMap<(usize,Box<[usize]>),usize>,
    stupid_typemap:HashMap<usize,Vec<(usize,usize)>>,
    placeholderfunc:Option<usize>,
    pair_hashes:HashMap<(usize,usize),usize>,
    l_hashes:HashMap<usize,usize>,
    r_hashes:HashMap<usize,usize>,
    pub values:Vec<(ProcValue,usize)>,
    pair_type_hashes:HashMap<(usize,usize),usize>,
    left_type_hashes:HashMap<usize,Vec<usize>>,
    right_type_hashes:HashMap<usize,Vec<usize>>,
    arrow_type_hashes:HashMap<(usize,usize),usize>,
    lr_type_hashes:HashMap<(usize,usize),usize>,
    l_type_hashes:HashMap<usize,Vec<usize>>,
    r_type_hashes:HashMap<usize,Vec<usize>>,
    pub types:Vec<ProcType>,
    pub falseval:Option<usize>,
    pub trueval:Option<usize>,
    
    pub debug_type_names:HashMap<usize,String>
}
impl ExpressionBuilder {
    pub fn new()->ExpressionBuilder {
        ExpressionBuilder {
            functions:Vec::new(),
            functionmemo:HashMap::new(),
            stupid_typemap:HashMap::new(),
            placeholderfunc:None,
            pair_hashes:HashMap::new(),
            l_hashes:HashMap::new(),
            r_hashes:HashMap::new(),
            values:vec![(Uneval,0),(UnitValue,0)],
            pair_type_hashes:HashMap::new(),
            left_type_hashes:HashMap::new(),
            right_type_hashes:HashMap::new(),
            arrow_type_hashes:HashMap::new(),
            lr_type_hashes:HashMap::new(),
            l_type_hashes:HashMap::new(),
            r_type_hashes:HashMap::new(),
            types:vec![UnitType],
            falseval:None,
            trueval:None,

            debug_type_names:HashMap::new()
        }
    }

    pub fn get_f_handle(&self,handle:usize) -> usize {self.functions[handle].concval}
    pub fn get_f_count(&self) -> usize {self.functions.len()}
    pub fn get_function_placeholder(&mut self) -> usize {
        let nval=self.values.len();
        self.values.push((FuncAsValue(self.functions.len()),1));
        if self.placeholderfunc.is_some() {panic!()}
        self.placeholderfunc=Some(nval);
        nval
    }
    pub fn insert_function(&mut self,mut f:Dsl,tys:Vec<usize>,resultant:usize) -> usize {
        let args = match f {TransferStack(fp,amt)=>{f=*fp;amt} _=>0};
        if args<tys.len() {
            f=self.get_applied(Self::bump(&f,tys.len()-args,0),(0..tys.len()-args).rev().map(|x|AccessStack(x)).collect());
        }
        if args>tys.len() {panic!()}
        for (i,arg) in tys.iter().enumerate() {
            self.stupid_typemap.entry(*arg).or_default().push((self.functions.len(),i));
        }
        match self.placeholderfunc {
            Some(x)=>{
                self.placeholderfunc=None;
                self.functions.push(FunctionEntry{dsl:Rc::new(f),concval:x,argtypes:tys,restype:resultant});x
            }
            None=>{
                let nval=self.values.len();
                self.values.push((FuncAsValue(self.functions.len()),1));
                self.functions.push(FunctionEntry{dsl:Rc::new(f),concval:nval,argtypes:tys,restype:resultant});nval
            }
        }
    }

    
    pub fn get_required_function_args(&self,f:usize) -> Option<usize> {self.functions.get(f).map(|FunctionEntry{argtypes:a,..}|a.len())}
    pub fn exec_function(&mut self,f:usize,args:Vec<usize>) -> usize {
        let nargs = args.into_boxed_slice();
        match self.functionmemo.entry((f,nargs.clone())) {
            Occupied(x) => *x.get(),
            Vacant(_) => {
                let trsh = self.functions[f].dsl.clone();
                match self.substitute(&trsh,0,0,Rc::new(vec![(nargs.into_iter().rev().map(|x|BaseValue(*x)).collect(),0)])) {
                    BaseValue(y)=>{self.functionmemo.insert((f,nargs),y);y},_=>panic!()
                }
            }
        }
    }

    pub fn get_placeholder_type(&mut self) -> usize {self.types.push(Placeholder);self.types.len()-1}
    pub fn get_unit_type(&self) -> usize {0}
    pub fn get_unit_value(&self) -> usize {1}
    pub fn get_pair_type(&mut self,a:usize,b:usize)->usize {
        match self.pair_type_hashes.entry((a,b)) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.types.len();
                self.types.push(PairType(a,b));
                x.insert(nval);
                self.left_type_hashes.entry(a).or_default().push(nval);
                self.right_type_hashes.entry(b).or_default().push(nval);
                nval
            }
        }
    }
    pub fn place_lr_type_in_placeholder(&mut self,a:usize,b:usize,c:usize) {
        self.types[c]=LRType(a,b);
        self.lr_type_hashes.insert((a,b),c);
        self.l_type_hashes.entry(a).or_default().push(c);
        self.r_type_hashes.entry(b).or_default().push(c);
    }
    pub fn get_lr_type(&mut self,a:usize,b:usize)->usize {
        match self.lr_type_hashes.entry((a,b)) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.types.len();
                self.types.push(LRType(a,b));
                x.insert(nval);
                self.l_type_hashes.entry(a).or_default().push(nval);
                self.r_type_hashes.entry(b).or_default().push(nval);
                nval
            }
        }
    }
    pub fn get_arrow_type(&mut self,a:usize,b:usize)->usize {
        match self.arrow_type_hashes.entry((a,b)) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.types.len();
                self.types.push(ArrowType(a,b));
                x.insert(nval);
                nval
            }
        }
    }
    pub fn get_pair(&mut self,a:usize,b:usize)->usize {
        if a==0 || b==0 {return 0}
        match self.pair_hashes.entry((a,b)) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.values.len();
                self.values.push((PairValue(a,b),self.values[a].1+self.values[b].1+1));
                x.insert(nval);
                nval
            }
        }
    }
    pub fn get_l(&mut self,a:usize)->usize {
        if a==0 {return 0}
        match self.l_hashes.entry(a) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.values.len();
                self.values.push((LValue(a),self.values[a].1+1));
                x.insert(nval);
                nval
            }
        }
    }
    pub fn get_r(&mut self,a:usize)->usize {
        if a==0 {return 0}
        match self.r_hashes.entry(a) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.values.len();
                self.values.push((RValue(a),self.values[a].1+1));
                x.insert(nval);
                nval
            }
        }
    }
}



pub fn build_ntfa(
    builder:&mut ExpressionBuilder,
    input:usize,input_type:usize,
    output:Option<BaseLiteral>,output_type:usize,
    confirmer:&Confirmer,
    previous_accepting_states:&HashMap<usize,HashSet<usize>>,
    k:usize
)->(NTFA,HashSet<usize>) {
    let mut res = NTFA::new();
    //state space:
    // 0:uneval
    // 1:()
    //function space:
    // 0:unit        (0)
    // 1:input       (0)
    // 2:pair        (2)
    // 3:fst         (1)
    // 4:snd         (1)
    // 5:inl         (1)
    // 6:inr         (1)
    // 7:unl         (1)
    // 8:unr         (1)
    // 9:switch      (3)
    // 10:recursion  (1)
    // 11-onwards: free space!
    res.add_nullary(0,1);
    res.add_nullary(1,input);
    res.add_nullary(0,0);
    res.add_nullary(1,0);
    res.add_rule(2,0,vec![0,0]);
    res.add_rule(3,0,vec![0]);
    res.add_rule(4,0,vec![0]);
    res.add_rule(5,0,vec![0]);
    res.add_rule(6,0,vec![0]);
    res.add_rule(7,0,vec![0]);
    res.add_rule(8,0,vec![0]);
    res.add_rule(9,0,vec![0,0,0]);
    res.add_rule(10,0,vec![0]);
    for ff in 0..builder.get_f_count() {
        res.add_rule(1+ff,0,vec![0;builder.get_required_function_args(ff).unwrap()]);
    }
    let mut single_dedup : HashSet<usize> = HashSet::new();
    let mut processed : HashSet<usize> = HashSet::new();
    let mut processed_rel : HashMap<usize,Vec<(usize,usize)>> = HashMap::new();
    let mut queue : BinaryHeap<QueueElem<(usize,Vec<usize>)>> = BinaryHeap::new();
    queue.push(QueueElem{item:(1,vec![0]),priority:1});
    queue.push(QueueElem{item:(input,vec![input_type]),priority:1});
    let mut visited : HashMap<(usize,usize),usize> = HashMap::new();//x with type y is obtained with size z
    let mut accepting_states = HashSet::new();
    while let Some(QueueElem{item:(x,mut xtl),priority:size}) = queue.pop() {
        if size>=k {break;}
        xtl.retain(|xt|{
            match visited.entry((x,*xt)) {
                Occupied(_)=>false,
                Vacant(y)=>{y.insert(size);true}
            }
        });
        if xtl.len()==0 {continue;}
        let xtl=xtl;//remove mutability
        let mut res_l = Vec::new();
        let mut res_r = Vec::new();
        let mut res_ul = Vec::new();
        let mut res_ur = Vec::new();
        let mut res_fst = Vec::new();
        let mut res_snd = Vec::new();
        for xt in xtl.iter() {
            if let Some(l_up) = builder.l_type_hashes.get(&xt) {
                res_l.extend(l_up.iter().copied());
            }
            if let Some(r_up) = builder.r_type_hashes.get(&xt) {
                res_r.extend(r_up.iter().copied());
            }
            match &builder.types[*xt] {
                PairType(a,b) => {
                    res_fst.push(*a);
                    res_snd.push(*b);
                }
                LRType(a,b) => {
                    res_ul.push(*a);
                    res_ur.push(*b);
                }
                _ => {}
            }
        }
        match &builder.values[x].0 {
            PairValue(y,z)=>{
                res.add_rule(3,x,vec![*y]);
                res.add_rule(4,x,vec![*z]);
                queue.push(QueueElem{item:(*y,res_fst),priority:size+1});
                queue.push(QueueElem{item:(*z,res_snd),priority:size+1});
            }
            _=>{}
        }
        if res_l.len()>0 {
            let nh = builder.get_l(x);
            res.add_rule(5,x,vec![nh]);
            queue.push(QueueElem{item:(nh,res_l),priority:size+1});
        }
        if res_r.len()>0 {
            let nh = builder.get_r(x);
            res.add_rule(6,x,vec![nh]);
            queue.push(QueueElem{item:(nh,res_r),priority:size+1});
        }
        match &builder.values[x].0 {
            LValue(y)=>{
                res.add_rule(7,x,vec![*y]);
                queue.push(QueueElem{item:(*y,res_ul),priority:size+1});
            }
            RValue(y)=>{
                res.add_rule(8,x,vec![*y]);
                queue.push(QueueElem{item:(*y,res_ur),priority:size+1});
            }
            _=>{}
        }
        for xt in xtl.iter() {
            let oua = if let Some(y) = &output {y.accepts(x)} else {true};
            if *xt == output_type && oua && confirmer.accepts(builder,input,x) {
                accepting_states.insert(x);
            }
            if *xt == input_type && builder.values[input].1>builder.values[x].1 {
                if let Some(z) = previous_accepting_states.get(&x) {
                    for bub in z {
                        res.add_rule(10,x,vec![*bub]);
                        queue.push(QueueElem{item:(*bub,vec![output_type]),priority:size+1});
                    }
                } else {
                    println!("-=-=-=-=-=-=-=-=-=-=-=-=- ntfa tried to get accepting states of state that hasn't been calculated yet!");
                }
            }
            if let Some(z) = builder.stupid_typemap.get(&xt) {
                let z=z.clone();
                for (f_ind,s_ind) in z.iter() {
                    let FunctionEntry {argtypes,restype,..} = &builder.functions[*f_ind];
                    let restype=*restype;
                    let mut cartesian = vec![(Vec::new(),0)];
                    for (i,argtype) in argtypes.into_iter().enumerate() {
                        if i==*s_ind {
                            for (c,ss) in cartesian.iter_mut() {c.push(x);*ss+=size}
                            continue;
                        }
                        let mut swap_buf = Vec::new();
                        if let Some(v) = processed_rel.get(&argtype) {
                            for (u,usi) in v.iter() {
                                for (cart,csize) in cartesian.iter() {
                                    swap_buf.push({let mut cc=cart.clone();cc.push(*u);(cc,csize+usi)});
                                }
                            }
                        }
                        if swap_buf.len()==0 {break;}
                        cartesian=swap_buf;
                    }
                    for (mut cart,csize) in cartesian.into_iter() {
                        let exec = builder.exec_function(*f_ind,cart.clone());
                        let rf = cart.remove(0);
                        cart.push(exec);
                        res.add_rule(11+*f_ind,rf,cart);
                        queue.push(QueueElem{item:(exec,vec![restype]),priority:csize+1});
                    }
                }
            }
            if let Some(z) = builder.left_type_hashes.get(&xt) {
                let z=z.clone();
                for w in z.iter() {
                    let r = match &builder.types[*w] {PairType(_,r)=>r,_=>panic!()};
                    if let Some(v) = processed_rel.get(&r) {
                        for (u,usi) in v.iter() {
                            let merged = builder.get_pair(x,*u);
                            res.add_rule(2,x,vec![*u,merged]);
                            queue.push(QueueElem{item:(merged,vec![*w]),priority:usi+size+1});
                        }
                    }
                }
            }
            if let Some(z) = builder.right_type_hashes.get(&xt) {
                let z=z.clone();
                for w in z.iter() {
                    let l = match &builder.types[*w] {PairType(l,_)=>l,_=>panic!()};
                    if let Some(v) = processed_rel.get(&l) {
                        for (u,usi) in v.iter() {
                            let merged = builder.get_pair(*u,x);
                            res.add_rule(2,*u,vec![x,merged]);
                            queue.push(QueueElem{item:(merged,vec![*w]),priority:usi+size+1});
                        }
                    }
                }
            }
        }
        if !single_dedup.contains(&x) {
            single_dedup.insert(x);
            processed.insert(x);
            for y in processed.iter() {
                match &builder.values[*y].0 {
                    LValue(_)=>{res.add_rule(9,*y,vec![x,0,x]);}
                    RValue(_)=>{res.add_rule(9,*y,vec![0,x,x]);}
                    _=>{}
                }
                match &builder.values[x].0 {
                    LValue(_)=>{res.add_rule(9,x,vec![*y,0,*y]);}
                    RValue(_)=>{res.add_rule(9,x,vec![0,*y,*y]);}
                    _=>{}
                }
            }
        }
        for xt in xtl.iter() {
            processed_rel.entry(*xt).or_default().push((x,size));
        }//processed_rel is meant to have duplicate entries: one for each type.
    }
    (res,accepting_states)
}












