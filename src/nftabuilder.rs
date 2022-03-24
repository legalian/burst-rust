

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::hash_map::Entry::*;
use crate::nfta::{*};
use crate::spec::{*};
use crate::dsl::{*};
use crate::queue::{*};
use Dsl::{*};
use Transition::{*};
use TermClassification::{*};

#[derive(Debug)]
pub enum ProcType {
    EnumType(Vec<Vec<usize>>),
    ArrowType(usize,usize),
    Placeholder
}
use ProcType::{*};

#[derive(Debug)]
pub enum ProcValue {
    Const(usize,Vec<usize>),
    FuncAsValue(usize),
    Uneval
}
use ProcValue::{*};

#[derive(Debug)]
pub struct FunctionEntry {
    dsl:Rc<Dsl>,
    pub concval:usize,
    pub argtypes:Vec<usize>,
    pub restype:usize
}

#[derive(Clone,Copy,PartialEq,Eq,PartialOrd,Ord,Hash,Debug)]
pub enum TypeMapType {
    Constructor(usize),
    Function(usize)
}
use TypeMapType::{*};
pub struct ConstructorEntry {
    pub argtypes:Vec<usize>,
    pub restype:usize,
    pub index:usize,
    pub name:Option<String>
}
pub struct ExpressionBuilder {
    pub functions:Vec<FunctionEntry>,
    functionmemo:HashMap<(usize,Box<[usize]>),usize>,
    pub stupid_typemap:HashMap<usize,Vec<(TypeMapType,usize)>>,
    placeholderfunc:Option<usize>,
    value_hashes:HashMap<(usize,Vec<usize>),usize>,
    pub values:Vec<(ProcValue,usize)>,
    tuple_hashes:HashMap<Vec<usize>,(usize,usize)>,
    arrow_type_hashes:HashMap<(usize,usize),usize>,
    pub types:Vec<ProcType>,


    temporary_recursive_memo:Option<(Rc<RefCell<HashMap<usize,usize>>>,Rc<Dsl>,Vec<usize>)>,

    pub debug_type_names:HashMap<usize,String>,
    pub constructors:Vec<ConstructorEntry>,

    pub nat_type:Option<usize>,
    pub bool_type:Option<usize>

    // pub debug_constr_names:HashMap<usize,Constname>,//type,value
}
impl ExpressionBuilder {
    pub fn new()->ExpressionBuilder {
        ExpressionBuilder {
            functions:Vec::new(),
            constructors:Vec::new(),
            functionmemo:HashMap::new(),
            stupid_typemap:HashMap::new(),

            placeholderfunc:None,
            value_hashes:HashMap::new(),
            values:vec![(Uneval,0)],

            tuple_hashes:HashMap::new(),

            arrow_type_hashes:HashMap::new(),
            types:Vec::new(),

            temporary_recursive_memo:None,

            debug_type_names:HashMap::new(),
            // debug_constr_names:HashMap::new()

            nat_type:None,
            bool_type:None
        }
    }
    pub fn force_get_nat(&mut self) -> usize {//O, S
        match self.nat_type {
            Some(x)=>x,
            None=>{
                let f = self.get_placeholder_type();
                self.place_type_in_placeholder(f,vec![vec![],vec![f]],vec![String::from("O"),String::from("S")]);
                self.nat_type = Some(f);f
            }
        }
    }
    pub fn force_get_bool(&mut self) -> usize {//False, True
        match self.bool_type {
            Some(x)=>x,
            None=>{
                let f = self.get_placeholder_type();
                self.place_type_in_placeholder(f,vec![vec![],vec![]],vec![String::from("False"),String::from("True")]);
                self.bool_type = Some(f);f
            }
        }
    }
    pub fn get_constructors_for(&self,ty:usize)->Vec<usize> {
        self.constructors.iter().enumerate().filter_map(|(i,c)|if c.restype==ty {Some(i)} else {None}).collect()
    }
    pub fn get_nullary_constructors(&self)->Vec<usize> {
        self.constructors.iter().enumerate().filter_map(|(i,c)|if c.argtypes.len()==0 {Some(i)} else {None}).collect()
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
            self.stupid_typemap.entry(*arg).or_default().push((Function(self.functions.len()),i));
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
    pub fn evaluate_solitary(&mut self,a:&Dsl,arg:usize) -> Option<usize> {
        match self.substitute(&a,0,0,Rc::new(vec![(vec![BaseValue(arg)],0)])) {
            BaseValue(y)=>Some(y),
            _=>None
            // k=>panic!("failed to resolve to concrete value! \nfunction: {:#?}\n{:?}\n{:?}\n",a,DebugValue{t:arg,expr:self},k)
        }
    }
    pub fn exec_interior_recursive_function(&mut self,arg:usize) -> usize {
        let whatev = &mut self.temporary_recursive_memo.as_mut().unwrap().2;
        let tsize = self.values[arg].1;
        if let Some(z) = whatev.last() {
            if tsize >= *z {
                return 0;
            }
        }
        whatev.push(tsize);
        if let Some(z) = self.temporary_recursive_memo.as_ref().unwrap().0.borrow_mut().get(&arg) {
            return *z;
        }
        let trsh = self.temporary_recursive_memo.as_ref().unwrap().1.clone();
        let res = match self.evaluate_solitary(&trsh,arg){
            Some(z)=>{self.temporary_recursive_memo.as_ref().unwrap().0.borrow_mut().insert(arg,z);z},
            None=>panic!()
        };
        self.temporary_recursive_memo.as_mut().unwrap().2.pop();
        res
    }
    pub fn eval_recursive_function(&mut self,func:Rc<Dsl>,temp:Rc<RefCell<HashMap<usize,usize>>>,arg:usize) -> usize {
        self.temporary_recursive_memo = Some((temp,func.clone(),Vec::new()));
        let res = self.exec_interior_recursive_function(arg);
        self.temporary_recursive_memo = None; res
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
    pub fn get_placeholder_type(&mut self) -> usize {self.types.push(Placeholder);self.types.len()-1}
    pub fn get_tuple_type(&mut self,a:Vec<usize>)->(usize,usize) {//first is type, second is constructor index
        match self.tuple_hashes.entry(a) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                for (i,arg) in x.key().iter().enumerate() {
                    self.stupid_typemap.entry(*arg).or_default().push((Constructor(self.constructors.len()),i));
                }
                let keyclone = x.key().clone();
                x.insert((self.types.len(),self.constructors.len()));
                self.constructors.push(ConstructorEntry {
                    argtypes:keyclone.clone(),
                    restype:self.types.len(),
                    index:0,
                    name:None
                });
                self.types.push(EnumType(vec![keyclone]));
                (self.types.len()-1,self.constructors.len()-1)
            }
        }
    }
    pub fn place_type_in_placeholder(&mut self,a:usize,b:Vec<Vec<usize>>,names:Vec<String>)->Vec<usize> {
        let mut res = Vec::new();
        for (j,c) in b.iter().enumerate() {
            for (i,arg) in c.iter().enumerate() {
                self.stupid_typemap.entry(*arg).or_default().push((Constructor(self.constructors.len()),i));
            }
            res.push(self.constructors.len());
            self.constructors.push(ConstructorEntry {
                argtypes:c.clone(),
                restype:a,
                index:j,
                name:Some(names[j].clone())
            });
        }
        self.types[a] = EnumType(b);
        res
    }
    pub fn get_constructed(&mut self,a:usize,b:Vec<usize>)->usize {
        if b.contains(&0) {return 0;}
        match self.value_hashes.entry((a,b)) {
            Occupied(x)=>x.get().clone(),
            Vacant(x)=>{
                let nval=self.values.len();
                self.values.push((Const(a,x.key().1.clone()),x.key().1.iter().map(|z|self.values[*z].1).sum::<usize>()+1));
                x.insert(nval);
                nval
            }
        }
    }
}

impl<T:Clone> NFTABuilder<T> {
    pub fn new(input_type:usize,output_type:usize)->Self {
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
        NFTABuilder {
            input_type,output_type,
            paths:vec![(Vec::new(),Some(1),Vec::new())],//inner vec must be sorted
            // revhash:HashMap::new(),
            intersect_memo:HashMap::new(),
            // rename_memo:HashMap::new(),
            // subset_memo:HashMap::new(),
            // minification_queue:Vec::new(),
            purgeset:HashSet::new()
        }
    }
}

impl NFTABuilder<usize> {
    pub fn build_nfta(
        &mut self,
        builder:&mut ExpressionBuilder,
        input:usize,
        confirmer:&Confirmer,
        disjunct_spec:&mut SingleSpecDisjunct,
        subex:&mut SubexpressionFinder,
        k:usize,interp:usize
    )->Vec<usize> {
        let buildstrategy = RepetitionCount;
        let limiterstrategy = SizeLimited;
        enum LimitingStrategy {
            SizeLimited,
            NoLimit
        }
        use LimitingStrategy::{*};
        enum BuildStrategy {
            SizeCalculationStopAtRule,
            SizeCalculationStopAtNode,
            RepetitionCount,
        }
        use BuildStrategy::{*};
        let mut processed : Vec<(usize,usize,TermClassification,usize)> = Vec::new();
        let mut processed_rel : HashMap<usize,Vec<(usize,TermClassification,usize)>> = HashMap::new();//type:val,size
        let mut queue : BinaryHeap<QueueElem<(usize,usize,TermClassification)>> = BinaryHeap::new();
        let mut visited : HashMap<(usize,TermClassification),usize> = HashMap::new();
        let mut smaller_unbound_inputs : Vec<(usize,TermClassification)> = Vec::new();
        let SingleSpecElem {
            graph_buffer : ref mut res,
            ref mut accepting_states,
            ref mut term_size_limiter,
            state : ref mut output
        } = disjunct_spec.states.get_mut(&input).unwrap();
        let mut res = res;
        let mut accepting_states = accepting_states;
        let mut term_size_limiter = term_size_limiter;
        let mut output = output;
        if res.rules.len()==0 {
            res.add_rule(Input,Vec::new(),(input,Elimination));
            queue.push(QueueElem{item:(input,self.input_type,Elimination),priority:1});
            for nul in builder.get_nullary_constructors() {
                let resultant = builder.get_constructed(nul,Vec::new());
                let rtype = builder.constructors[nul].restype;
                res.add_rule(Transition::Construct(nul),Vec::new(),(resultant,Introduction));
                queue.push(QueueElem{item:(resultant,rtype,Introduction),priority:1});
            }
        }
        while let Some(QueueElem{item:(x,xt,fresh),priority:size}) = queue.pop() {
            if size>k {break;}
            match visited.entry((x,fresh)) {
                Occupied(p)=>{
                    if *p.get()>size {panic!()}
                    continue;
                },
                Vacant(y)=>{y.insert(size);}
            }
            // println!("processing: {} {} {:?}",size,k,DebugValue{t:x,expr:builder});
            if xt == self.input_type && subex.compare_strictlysmaller(builder,x,input).ok() {
                let we = disjunct_spec.states.get(&x).cloned();
                let o = disjunct_spec.states.get_mut(&input).unwrap();
                res = &mut o.graph_buffer;
                accepting_states = &mut o.accepting_states;
                term_size_limiter = &mut o.term_size_limiter;
                output = &mut o.state;        
                match we {
                    Some(b)=>{
                        let bacc = b.accepting_states.clone();
                        for (bub,_) in bacc {
                            res.add_rule(Recursion,vec![(x,fresh)],(bub,Elimination));
                            queue.push(QueueElem{item:(bub,self.output_type,Elimination),priority:size+1});
                        }
                    }
                    None => {
                        smaller_unbound_inputs.push((x,fresh));
                        if let Some(z) = processed_rel.get(&self.output_type) {
                            for (z,zfresh,_) in z {
                                res.add_rule(Recursion,vec![(x,fresh)],(*z,*zfresh));
                            }
                        }
                    }
                }
            }
            // res.add_rule(Constant(x),Vec::new(),x);
            if let Elimination = fresh {
                match (&builder.values[x].0,&builder.types[xt]) {
                    (Const(j,y),EnumType(v))=>{
                        for (i,(y,yt)) in y.iter().zip(v[builder.constructors[*j].index].iter()).enumerate() {
                            if let SizeLimited = &limiterstrategy {
                                if *term_size_limiter+builder.values[input].1 <= builder.values[*y].1 {
                                    continue;
                                }
                            }
                            if let SizeCalculationStopAtRule = &buildstrategy {
                                if size>=k {continue;}
                            }
                            res.add_rule(Destruct(*j,i),vec![(x,fresh)],(*y,Elimination));
                            if let SizeCalculationStopAtNode = &buildstrategy {
                                if size>=k {continue;}
                            }
                            queue.push(QueueElem{item:(*y,*yt,Elimination),priority:size+1});
                        }
                    }
                    _=>{}
                }
            }
            processed.push((x,xt,fresh,size));
            if let Elimination = fresh {
                for (y,yt,yfresh,ysize) in processed.iter() {
                    if let SizeCalculationStopAtRule = &buildstrategy {
                        if *ysize+2*size>=k {continue;}
                    }
                    match (&builder.values[x].0,&builder.types[xt]) {
                        (Const(j,_),EnumType(v)) if v.len()>1 =>{
                            let index = builder.constructors[*j].index;
                            let mut nvm = vec![(x,fresh)];
                            nvm.resize(1+v.len(),(0,Introduction));
                            nvm[index+1]=(*y,*yfresh);
                            res.add_rule(Switch(v.len()),nvm,(*y,Introduction));
                            if let SizeCalculationStopAtNode = &buildstrategy {
                                if *ysize+2*size>=k {continue;}
                            }
                            queue.push(QueueElem{item:(*y,*yt,Introduction),
                                priority:if let RepetitionCount = &buildstrategy {size+1} else {*ysize+2*size+1}
                            });
                        }
                        _=>{}
                    }
                }
            }
            for (y,yt,yfresh,ysize) in processed.iter() {
                if let Elimination = yfresh {
                    if let SizeCalculationStopAtRule = &buildstrategy {
                        if 2*ysize+size>=k {continue;}
                    }
                    match (&builder.values[*y].0,&builder.types[*yt]) {
                        (Const(j,_),EnumType(v)) if v.len()>1 =>{
                            let index = builder.constructors[*j].index;
                            let mut nvm = vec![(*y,*yfresh)];
                            nvm.resize(1+v.len(),(0,Introduction));
                            nvm[index+1]=(x,fresh);
                            res.add_rule(Switch(v.len()),nvm,(x,Introduction));
                            if let SizeCalculationStopAtNode = &buildstrategy {
                                if 2*ysize+size>=k {continue;}
                            }
                            queue.push(QueueElem{item:(x,xt,Introduction),
                                priority:if let RepetitionCount = &buildstrategy {size+1} else {2*ysize+size+1}
                            });
                        }
                        _=>{}
                    }
                }
            }
            if xt==self.output_type {
                for z in smaller_unbound_inputs.iter() {
                    res.add_rule(Recursion,vec![*z],(x,fresh));
                }
                if output.accepts(x) && confirmer.accepts(builder,input,x) {
                    accepting_states.insert((x,fresh));
                }
            }
            processed_rel.entry(xt).or_default().push((x,fresh,size));
            if let Some(z) = builder.stupid_typemap.get(&xt) {
                let z=z.clone();
                for (f_ind,s_ind) in z.iter() {
                    let (argtypes,restype) = match f_ind {
                        Function(x)=>{
                            let FunctionEntry {argtypes,restype,..} = &builder.functions[*x];
                            (argtypes,restype)
                        }
                        Constructor(x)=>{
                            let ConstructorEntry {argtypes,restype,..} = &builder.constructors[*x];
                            (argtypes,restype)
                        }
                    };
                    let restype=*restype;
                    let mut cartesian = vec![(Vec::new(),0)];
                    for (i,argtype) in argtypes.into_iter().enumerate() {
                        if i==*s_ind {
                            for (c,ss) in cartesian.iter_mut() {c.push((x,fresh));*ss+=size}
                            // println!("operated on cartesian {:?}",cartesian);
                            continue;
                        }
                        let mut swap_buf = Vec::new();
                        if let Some(v) = processed_rel.get(&argtype) {
                            for (u,ufresh,usi) in v.iter() {
                                for (cart,csize) in cartesian.iter() {
                                    swap_buf.push({let mut cc=cart.clone();cc.push((*u,*ufresh));(cc,csize+usi)});
                                }
                            }
                        }
                        cartesian=swap_buf;
                        if cartesian.len()==0 {break;}
                    }
                    for (cart,csize) in cartesian.into_iter() {
                        if let SizeCalculationStopAtRule = &buildstrategy {
                            if csize>=k {continue;}
                        }
                        let exec = match f_ind {
                            Constructor(x)=>builder.get_constructed(*x,cart.iter().map(|(k,_)|*k).collect()),
                            Function(x)=>builder.exec_function(*x,cart.iter().map(|(k,_)|*k).collect())
                        };
                        if let SizeLimited = &limiterstrategy {
                            if *term_size_limiter+builder.values[input].1 <= builder.values[exec].1 {
                                continue;
                            }
                        }
                        match f_ind {
                            Constructor(x)=>{
                                res.add_rule(Transition::Construct(*x),cart,(exec,Introduction));
                            }
                            Function(x)=>{
                                res.add_rule(ArbitraryFunc(*x),cart,(exec,Introduction));
                            }
                        }
                        if let SizeCalculationStopAtNode = &buildstrategy {
                            if csize>=k {continue;}
                        }
                        queue.push(QueueElem{item:(exec,restype,Introduction),
                            priority:if let RepetitionCount = &buildstrategy {size+1} else {csize+1}
                        });
                    }
                }
            }
        }
        // let StackElem {
        //     input,
        //     res,
        //     accepting_states,
        //     ..
        // } = stack.pop().unwrap();
        // graph_buffer.insert(input,res);
        // previous_accepting_states.insert(input,accepting_states);
        // }
        // let res = graph_buffer.remove(&input).unwrap();
        // println!("converting... {} states...",res.rules.len());
        res.convert(self,&accepting_states.iter().copied().collect(),interp,NoMapping)
    }
}



