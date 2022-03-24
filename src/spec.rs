

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_map::Entry::*;

use crate::nftabuilder::{*};
use crate::nfta::{*};
use RefineLiteral::{*};
use ProcValue::{*};


#[derive(Clone)]
pub enum Confirmer {
    Nothing,
    CheckPred(usize),
    CheckFunc(usize)
}
use Confirmer::{*};
impl Confirmer {
    pub fn accepts(&self,ex:&mut ExpressionBuilder,input:usize,output:usize) -> bool {
        match self {
            Nothing => true,
            CheckPred(_) => {
                panic!();
                // let tv = ex.trueval.unwrap();
                // let fv = ex.falseval.unwrap();
                // let res = ex.exec_function(*f,vec![input,output]);
                // if res==tv {true}
                // else if res==fv {false}
                // else {panic!()}
            }
            CheckFunc(f) => output == ex.exec_function(*f,vec![input])
        }
    }
}

#[derive(Clone)]
pub enum SpecVariant {
    JustIO(Spec),
    ConfirmWithFunc(Spec,usize),
    ReferenceImpl(usize)
}
use SpecVariant::{*};
impl SpecVariant {
    pub fn is_valid(&self)->bool {
        match self {
            JustIO(w) => w.truesets.len()>0,
            _=>panic!("not supported yet!")
        }
    }
    pub fn refine(&mut self,a:usize,lit:RefineLiteral) {
        match self {
            JustIO(w) => w.refine(a,lit),
            _=>panic!("not supported yet!")
        }
    }
    pub fn get_truesets(&mut self)->&mut [SingleSpecDisjunct] {
        match self {
            JustIO(w) => &mut w.truesets,
            _=>panic!("not supported yet!")
        }
    }
    pub fn refine_disjoint(&mut self,lits:&[(usize,RefineLiteral)])->SpecVariant {
        match self {
            JustIO(w) => JustIO(w.refine_disjoint(lits)),
            _=>panic!("not supported yet!")
        }
    }
    pub fn getconfirmer(&self) -> Confirmer {
        match self {
            JustIO(_) => Nothing,
            ConfirmWithFunc(_,a) => CheckPred(*a),
            ReferenceImpl(a) => CheckFunc(*a)
        }
    }
}



#[derive(Clone,Debug,Copy)]
pub enum RefineLiteral {
    EqLit(usize),
    NeqLit(usize)
}
// use RefineLiteral::{*};
impl RefineLiteral {
    pub fn accepts(&self,a:usize) -> bool {
        match self {
            EqLit(x) => *x == a,
            NeqLit(x) => *x != a
        }
    }
    fn implies(&self,other:&RefineLiteral) -> bool {
        match (self,other) {
            (EqLit(x),NeqLit(y)) => x != y,
            (NeqLit(x),NeqLit(y)) => x == y,
            (EqLit(x),EqLit(y)) => x == y,
            _=>false
        }
    }
    fn conflicts(&self,other:&RefineLiteral) -> bool {
        match (self,other) {
            (EqLit(x),NeqLit(y)) => x == y,
            (NeqLit(x),EqLit(y)) => x == y,
            (EqLit(x),EqLit(y)) => x != y,
            _=>false
        }
    }
}
#[derive(Clone,Debug)]
pub enum BaseLiteral {
    BaseEq(usize),
    BaseNeq(HashSet<usize>)
}
use BaseLiteral::{*};
impl BaseLiteral {
    pub fn accepts(&self,a:usize) -> bool {
        match self {
            BaseEq(x) => *x == a,
            BaseNeq(y) => !y.contains(&a)
        }
    }
    pub fn negate_into_disjunct(&self,into:&mut Vec<RefineLiteral>) {
        match self {
            BaseEq(x) => {into.push(NeqLit(*x));}
            BaseNeq(y) => {
                for x in y.iter() {
                    into.push(EqLit(*x));
                }
            }
        }
    }
    fn implies(&self,other:&RefineLiteral) -> bool {
        match (self,other) {
            (BaseEq(x),NeqLit(y)) => x != y,
            (BaseNeq(x),NeqLit(y)) => x.contains(y),
            (BaseEq(x),EqLit(y)) => x == y,
            _=>false
        }
    }
    fn conflicts(&self,other:&RefineLiteral) -> bool {
        match (self,other) {
            (BaseEq(x),NeqLit(y)) => x == y,
            (BaseNeq(x),EqLit(y)) => x.contains(y),
            (BaseEq(x),EqLit(y)) => x != y,
            _=>false
        }
    }
    fn from(other:&RefineLiteral) -> BaseLiteral {
        match other {
            EqLit(x) => BaseEq(*x),
            NeqLit(x) => BaseNeq({let mut h=HashSet::new();h.insert(*x);h})
        }
    }
    fn intersect(&mut self,other:&RefineLiteral) -> bool {
        match (&*self,other) {
            (BaseNeq(_),NeqLit(y)) => {match self {BaseNeq(x)=>{x.insert(*y)},_=>panic!()};true},
            (BaseEq(x),EqLit(y)) => if x == y {true} else {false},
            (BaseEq(x),NeqLit(y)) => if x != y {true} else {false},
            (BaseNeq(x),EqLit(y)) => if !x.contains(y) {*self=BaseEq(*y);true} else {false},
        }
    }
}


pub enum RComp {Same,Smaller,Unrelated}
use RComp::{*};
impl RComp { pub fn ok(&self)->bool {match self {Smaller=>true,_=>false}} }

#[derive(Clone,Debug)]
pub struct SingleSpecElem {
    pub graph_buffer : PartialNFTA<(usize,TermClassification)>,
    pub accepting_states : HashSet<(usize,TermClassification)>,
    pub term_size_limiter : usize,
    pub state : BaseLiteral
}
#[derive(Clone,Debug)]
pub struct SubexpressionFinder {
    subexpressions:HashMap<usize,HashSet<usize>>
}
impl SubexpressionFinder {
    pub fn new() -> Self {
        SubexpressionFinder {
            subexpressions:HashMap::new()
        }
    }
    pub fn compare_strictlysmaller(
        &mut self,
        builder:&ExpressionBuilder,
        a:usize,
        b:usize
    )->RComp {
        if a==b {return Same;}
        if builder.values[a].1>=builder.values[b].1 { return Unrelated }
        // else {return Smaller;} //uncomment this line to allow recursion into ANY smaller value
        if !self.subexpressions.contains_key(&b) {
            let mut stack = vec![b];
            'ou: while let Some(x) = stack.last() {
                if self.subexpressions.contains_key(&b) {continue;}
                match &builder.values[*x].0 {
                    Const(_,z) if z.len()>0 => {
                        let mut bmap = Vec::new();
                        for a in z.iter() {
                            if let Some(ax) = self.subexpressions.get(&a) {bmap.push(ax);}
                            else {stack.push(*a);continue 'ou;}
                        }
                        let mut hm:HashSet<usize> = if z.len()==1 {bmap[0].clone()} else {bmap[0].union(&bmap[1]).copied().collect()};
                        for u in 2..bmap.len() {hm=hm.union(&bmap[u]).copied().collect()}
                        for a in z.iter() {hm.insert(*a);}
                        let x = stack.pop().unwrap();
                        self.subexpressions.insert(x,hm);
                    }
                    _=>{
                        self.subexpressions.insert(*x,HashSet::new());
                        stack.pop();
                    }
                }
            }
        }
        if let Some(x) = self.subexpressions.get(&b) {
            if x.contains(&a) {return Smaller;}
        }
        match (&builder.values[a].0,&builder.values[b].0) {
            (Const(ax,ay),Const(bx,by)) if ax==bx => {//match compare_strictlysmaller(builder,self.subexpressions,*ax,*bx)
                let mut smaller = false;
                for (ay,by) in ay.iter().zip(by.iter()) {
                    match self.compare_strictlysmaller(builder,*ay,*by) {
                        Unrelated=>{return Unrelated}
                        Smaller=>{smaller=true;}
                        Same=>{}
                    }
                }
                if smaller {Smaller} else {Same}
            }//uncomment the following line to allow any expression where a subexpression was replaced by a strict subexpression.
            // (LValue(a),LValue(b))|(RValue(a),RValue(b))=>compare_strictlysmaller(builder,subexpressions,*a,*b),
            _=>Unrelated
        }
    }
}
#[derive(Clone,Debug)]
pub struct SingleSpecDisjunct {
    pub opnfta : Option<Vec<usize>>,
    pub states : HashMap<usize,SingleSpecElem>
}
impl SingleSpecDisjunct {
    pub fn refine(&mut self,a:usize,lit:RefineLiteral)->bool {
        self.opnfta = None;
        match self.states.entry(a) {
            Occupied(mut x)=>{
                let x = x.get_mut();
                if !x.state.intersect(&lit) {return false}
                x.accepting_states.retain(|(a,_)|lit.accepts(*a));
            }
            Vacant(x)=>{x.insert(SingleSpecElem {
                graph_buffer : PartialNFTA::new(),
                accepting_states : HashSet::new(),
                term_size_limiter : 2,
                state : BaseLiteral::from(&lit)
            });}
        }
        for (_,v) in self.states.iter_mut() {
            v.graph_buffer.refine(a,lit);
        }
        true
    }
}


#[derive(Clone,Debug)]
pub struct Spec {
    truesets:Vec<SingleSpecDisjunct>
}
impl Spec {
    pub fn new()->Self {
        Spec {
            truesets:vec![SingleSpecDisjunct{
                opnfta:None,
                states:HashMap::new()
            }]
        }
    }
    pub fn refine(&mut self,a:usize,lit:RefineLiteral) {
        odds::vec::VecExt::retain_mut(&mut self.truesets,|v|v.refine(a,lit));
    }
    pub fn refine_disjoint(&self,lits:&[(usize,RefineLiteral)])->Spec {
        let mut truesets = Vec::new();
        for (a,lit) in lits {
            for k in self.truesets.iter() {
                let mut f = k.clone();
                if f.refine(*a,*lit) {
                    truesets.push(f);
                }
            }
        }
        Spec {
            truesets
        }
    }
}


