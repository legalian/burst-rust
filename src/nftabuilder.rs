

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::hash_map::Entry::*;
use crate::ntfa::{*};
use crate::spec::{*};
use crate::dsl::{*};
use crate::queue::{*};
use crate::debug::{*};
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

#[derive(Debug)]
pub struct FunctionEntry {
    dsl:Rc<Dsl>,
    concval:usize,
    pub argtypes:Vec<usize>,
    pub restype:usize
}

pub enum Constname {
    LRSplit(Box<Constname>,Box<Constname>),
    NullaryName(String),
    UnaryName(String),
}


pub struct ExpressionBuilder {
    pub functions:Vec<FunctionEntry>,
    functionmemo:HashMap<(usize,Box<[usize]>),usize>,
    stupid_typemap:HashMap<usize,Vec<(usize,usize)>>,
    placeholderfunc:Option<usize>,
    pair_hashes:HashMap<(usize,usize),usize>,
    l_hashes:HashMap<usize,usize>,
    r_hashes:HashMap<usize,usize>,
    pub values:Vec<(ProcValue,usize)>,
    pair_type_hashes:HashMap<(usize,usize),usize>,
    pub left_type_hashes:HashMap<usize,Vec<usize>>,
    pub right_type_hashes:HashMap<usize,Vec<usize>>,
    arrow_type_hashes:HashMap<(usize,usize),usize>,
    lr_type_hashes:HashMap<(usize,usize),usize>,
    pub l_type_hashes:HashMap<usize,Vec<usize>>,
    pub r_type_hashes:HashMap<usize,Vec<usize>>,
    pub types:Vec<ProcType>,
    pub falseval:Option<usize>,
    pub trueval:Option<usize>,

    temporary_recursive_memo:Option<(Rc<RefCell<HashMap<usize,usize>>>,Rc<Dsl>)>,

    pub debug_type_names:HashMap<usize,String>,
    pub debug_constr_names:HashMap<usize,Constname>,//type,value
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

            temporary_recursive_memo:None,

            debug_type_names:HashMap::new(),
            debug_constr_names:HashMap::new()
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
        let result = match self.placeholderfunc {
            Some(x)=>{
                self.placeholderfunc=None;
                self.functions.push(FunctionEntry{dsl:Rc::new(f),concval:x,argtypes:tys,restype:resultant});x
            }
            None=>{
                let nval=self.values.len();
                self.values.push((FuncAsValue(self.functions.len()),1));
                self.functions.push(FunctionEntry{dsl:Rc::new(f),concval:nval,argtypes:tys,restype:resultant});nval
            }
        };
        return result
    }
    pub fn get_required_function_args(&self,f:usize) -> Option<usize> {self.functions.get(f).map(|FunctionEntry{argtypes:a,..}|a.len())}
    pub fn exec_function(&mut self,f:usize,args:Vec<usize>) -> usize {
        // if self.functions[f].argtypes.len()>args.len() {panic!("not enough arguments!")}
        let nargs = args.into_boxed_slice();
        match self.functionmemo.entry((f,nargs.clone())) {
            Occupied(x) => *x.get(),
            Vacant(_) => {
                let trsh = self.functions[f].dsl.clone();
                match self.substitute(&trsh,0,0,Rc::new(vec![(nargs.into_iter().rev().map(|x|BaseValue(*x)).collect(),0)])) {
                    BaseValue(y)=>{self.functionmemo.insert((f,nargs),y);y}
                    k=>panic!("failed to resolve to concrete value! \nfunction: {:#?}\n{:?}\n{:?}\n",self.functions[f].dsl,nargs,k)
                }
            }
        }
    }
    pub fn exec_interior_recursive_function(&mut self,arg:usize) -> usize {
        if let Some(z) = self.temporary_recursive_memo.as_ref().unwrap().0.borrow_mut().get(&arg) {
            return *z;
        }
        let trsh = self.temporary_recursive_memo.as_ref().unwrap().1.clone();
        match self.substitute(&trsh,0,0,Rc::new(vec![(vec![BaseValue(arg)],0)])) {
            BaseValue(y)=>{
                self.temporary_recursive_memo.as_ref().unwrap().0.borrow_mut().insert(arg,y);y
            } _=>panic!()
        }
    }
    pub fn eval_recursive_function(&mut self,func:Rc<Dsl>,temp:Rc<RefCell<HashMap<usize,usize>>>,arg:usize) -> usize {
        self.temporary_recursive_memo = Some((temp,func.clone()));
        let res = self.exec_interior_recursive_function(arg);
        self.temporary_recursive_memo = None; res
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

enum RComp {
    Same,
    Smaller,
    Unrelated
}
use RComp::{*};
impl RComp {
    fn ok(&self)->bool {
        match self {
            Smaller=>true,
            _=>false
        }
    }
}

fn compare_strictlysmaller(
    builder:&ExpressionBuilder,
    subexpressions : &mut HashMap<usize,HashSet<usize>>,
    a:usize,
    b:usize
)->RComp {
    if a==b {return Same;}
    if builder.values[a].1>=builder.values[b].1 { return Unrelated }
    // else {return Smaller;} //uncomment this line to allow recursion into ANY smaller value
    if let Some(x) = subexpressions.get(&b) {
        if x.contains(&a) {return Smaller;}
    }
    match (&builder.values[a].0,&builder.values[b].0) {
        (PairValue(ax,ay),PairValue(bx,by))=>match compare_strictlysmaller(builder,subexpressions,*ax,*bx) {
            st@(Same|Smaller)=>match (st,compare_strictlysmaller(builder,subexpressions,*ay,*by)) {
                (Same,Same)=>Same,
                (Smaller|Same,Smaller|Same)=>{
                    subexpressions.entry(b).or_default().insert(a);
                    Smaller
                }
                _=>Unrelated
            }
            _=>Unrelated
        }//uncomment the following line to allow any expression where a subexpression was replaced by a strict subexpression.
        // (LValue(a),LValue(b))|(RValue(a),RValue(b))=>compare_strictlysmaller(builder,subexpressions,*a,*b),
        _=>Unrelated
    }
}

impl NTFABuilder {
    pub fn new(builder:&mut ExpressionBuilder,input_type:usize,output_type:usize)->Self {
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
        NTFABuilder {
            input_type,output_type,
            paths:vec![
                (0..builder.get_f_count()).rev().map(|ff|(11+ff,vec![0;builder.get_required_function_args(ff).unwrap()]))
                .chain(vec![
                    (10,vec![0]),
                    (9,vec![0,0,0]),
                    (8,vec![0]),
                    (7,vec![0]),
                    (6,vec![0]),
                    (5,vec![0]),
                    (4,vec![0]),
                    (3,vec![0]),
                    (2,vec![0,0]),
                    (1,vec![]),
                    (0,vec![]),
                ]).collect()
            ],//inner vec must be sorted
            revhash:HashMap::new(),
            intersect_memo:HashMap::new(),
            // rename_memo:HashMap::new(),
            // subset_memo:HashMap::new(),
            // minification_queue:Vec::new(),
            purgeset:HashSet::new()
        }
    }
    pub fn build_ntfa(
        &mut self,
        builder:&mut ExpressionBuilder,
        input:usize,
        outputs:&HashMap<usize,BaseLiteral>,
        confirmer:&Confirmer,
        previous_accepting_states:&mut HashMap<usize,HashSet<usize>>,
        graph_buffer : &mut HashMap<usize,PartialNTFA>,
        subexpressions : &mut HashMap<usize,HashSet<usize>>,
        k:usize
    )->(Option<usize>,ValueMapper) {
    //     println!("-=-=-=-=-=-=-=-=-=- BEGINNING BUILD PHASE: {:?}",DebugTypedValue{val:input,ty:input_type,expr:builder});
        #[derive(Default)]
        struct StackElem {
            input : usize,
            output : Option<BaseLiteral>,
            res : PartialNTFA,
            processed : HashMap<usize,usize>,
            processed_rel : HashMap<usize,Vec<(usize,usize)>>,//type:val,size,rstatus
            queue : BinaryHeap<QueueElem<(usize,Vec<usize>,bool)>>,
            visited : HashMap<(usize,usize),(usize,bool)>,
            accepting_states : HashSet<usize>
        }
        fn new_stack_elem(
            input:usize,
            input_type:usize,
            outputs:&HashMap<usize,BaseLiteral>
        )->StackElem {
            let mut queue = BinaryHeap::new();
            let mut res = PartialNTFA::new();
            res.add_rule(0,Vec::new(),1);
            res.add_rule(1,Vec::new(),input);
            queue.push(QueueElem{item:(1,vec![0],true),priority:1});
            queue.push(QueueElem{item:(input,vec![input_type],true),priority:1});
            StackElem{
                input,
                output:outputs.get(&input).cloned(),
                queue:queue,
                res,
                ..Default::default()
            }
        }
        let mut stack : Vec<StackElem> = vec![new_stack_elem(
            input,
            self.input_type,
            outputs
        )];
        'stackloop: while let Some(StackElem{
            input,
            output,
            res,
            processed,
            processed_rel,
            queue,
            visited,
            accepting_states
        }) = stack.last_mut() {
            let input=*input;
            // let output=
            while let Some(QueueElem{item:(x,mut xtl,fresh),priority:size}) = queue.pop() {
                if size>=k {break;}
                xtl.retain(|xt|{
                    match visited.entry((x,*xt)) {
                        Occupied(mut y)=>{
                            let yg = *y.get();
                            if fresh && !yg.1 {
                                y.insert((yg.0,true));true
                            } else {false}
                        },
                        Vacant(y)=>{y.insert((size,fresh));true}
                    }
                });
                if xtl.len()==0 {continue;}
                let xtl=xtl;
                for xt in xtl.iter() {
                    if *xt == self.input_type && compare_strictlysmaller(builder,subexpressions,x,input).ok() {
                        println!("back to the drawing board. From {:?} to {:?}",DebugTypedValue{val:input,ty:self.input_type,expr:builder},DebugTypedValue{val:x,ty:self.input_type,expr:builder});
                        if !previous_accepting_states.contains_key(&x) {
                            queue.push(QueueElem{item:(x,xtl,fresh),priority:size});
                            stack.push(new_stack_elem(
                                x,
                                self.input_type,
                                outputs
                            ));
                            continue 'stackloop;
                        }
                    }
                }
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
                if fresh {
                    match &builder.values[x].0 {
                        PairValue(y,z)=>{
                            if *y!=1 {
                                res.add_rule(3,vec![x],*y);
                                queue.push(QueueElem{item:(*y,res_fst,true),priority:size+1});
                            }
                            if *z!=1 {
                                res.add_rule(4,vec![x],*z);
                                queue.push(QueueElem{item:(*z,res_snd,true),priority:size+1});
                            }
                        }
                        LValue(y)=>{
                            if *y!=1 {
                                res.add_rule(7,vec![x],*y);
                                queue.push(QueueElem{item:(*y,res_ul,true),priority:size+1});
                            }
                        }
                        RValue(y)=>{
                            if *y!=1 {
                                res.add_rule(8,vec![x],*y);
                                queue.push(QueueElem{item:(*y,res_ur,true),priority:size+1});
                            }
                        }
                        _=>{}
                    }
                }
                if res_l.len()>0 {
                    let nh = builder.get_l(x);
                    res.add_rule(5,vec![x],nh);
                    queue.push(QueueElem{item:(nh,res_l,false),priority:size+1});
                }
                if res_r.len()>0 {
                    let nh = builder.get_r(x);
                    res.add_rule(6,vec![x],nh);
                    queue.push(QueueElem{item:(nh,res_r,false),priority:size+1});
                }
                // println!("checkpoint...");
                for xt in xtl.iter() {
                    // println!("xtl...");
                    let oua = if let Some(y) = &output {y.accepts(x)} else {true};
                    if *xt == self.output_type && oua && confirmer.accepts(builder,input,x) {
                        accepting_states.insert(x);
                    }
                    if *xt == self.input_type && compare_strictlysmaller(builder,subexpressions,x,input).ok() {
                        for bub in &previous_accepting_states[&x] {
                            res.add_rule(10,vec![x],*bub);
                            queue.push(QueueElem{item:(*bub,vec![self.output_type],true),priority:size+1});
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
                                    // println!("operated on cartesian {:?}",cartesian);
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
                                cartesian=swap_buf;
                                if cartesian.len()==0 {break;}
                                // println!("increasing {:?} to {:?}",cartesian,swap_buf);
                            }
                            // println!("calling function: {:?} {:?}",argtypes,cartesian);
                            for (cart,csize) in cartesian.into_iter() {
                                // if csize>=k {continue;}
                                let exec = builder.exec_function(*f_ind,cart.clone());
                                res.add_rule(11+*f_ind,cart,exec);
                                queue.push(QueueElem{item:(exec,vec![restype],true),priority:csize+1});
                            }
                        }
                    }
                    if size*2<k {
                        if let Some(w) = builder.pair_type_hashes.get(&(*xt,*xt)) {
                            let w=*w;
                            let merged = builder.get_pair(x,x);
                            res.add_rule(2,vec![x,x],merged);
                            queue.push(QueueElem{item:(merged,vec![w],false),priority:size*2+1});
                        }
                    }
                    if let Some(z) = builder.left_type_hashes.get(&xt) {
                        let z=z.clone();
                        for w in z.iter() {
                            let r = match &builder.types[*w] {PairType(_,r)=>r,_=>panic!()};
                            if let Some(v) = processed_rel.get(&r) {
                                for (u,usi) in v.iter() {
                                    // if *usi+size>=k {continue;}
                                    let merged = builder.get_pair(x,*u);
                                    res.add_rule(2,vec![x,*u],merged);
                                    queue.push(QueueElem{item:(merged,vec![*w],false),priority:*usi+size+1});
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
                                    // if *usi+size>=k {continue;}
                                    let merged = builder.get_pair(*u,x);
                                    res.add_rule(2,vec![*u,x],merged);
                                    queue.push(QueueElem{item:(merged,vec![*w],false),priority:*usi+size+1});
                                }
                            }
                        }
                    }
                }
                if x!=1 && !processed.contains_key(&x) {
                    processed.insert(x,size);
                    for (y,ysize) in processed.iter() {
                        // if *ysize+size>=k {continue;}
                        match &builder.values[*y].0 {
                            LValue(_)=>{res.add_rule(9,vec![*y,x,0],x);}
                            RValue(_)=>{res.add_rule(9,vec![*y,0,x],x);}
                            _=>{}
                        }
                        match &builder.values[x].0 {
                            LValue(_)=>{res.add_rule(9,vec![x,*y,0],*y);}
                            RValue(_)=>{res.add_rule(9,vec![x,0,*y],*y);}
                            _=>{}
                        }
                    }
                }
                for xt in xtl.iter() {
                    processed_rel.entry(*xt).or_default().push((x,size));
                }//processed_rel is meant to have duplicate entries: one for each type.
            }
            let StackElem{
                input,
                res,
                accepting_states,
                ..
            } = stack.pop().unwrap();
            // println!("{:?} resulted in: {:#?}",DebugValue{t:input,expr:builder},res);
            // println!("constructed one.");
            // println!("determinizing...");
            // res.determinize();
            // println!("converting...");
            // if accepting_states.len()==0 {return None}
            // if accepting_states.len()>1 {
            //     panic!("needs some more development...")
            // }
            graph_buffer.insert(input,res);
            // println!("converted!");
            
            previous_accepting_states.insert(input,accepting_states);
        }
        // println!("converting...");
        let accepting_states : Vec<_> = previous_accepting_states[&input].iter().copied().collect();
        let (states,vm) = graph_buffer.remove(&input).unwrap().convert(self,&accepting_states);
        (self.simplify(states),vm)
    }
}



