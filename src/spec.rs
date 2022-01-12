

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::hash_map::Entry::*;
use std::mem::take;

//here is a spec object that is specialized for use by BURST

use crate::cluster::Cluster;
use crate::graph::{Graph,GraphBox};
use crate::nftabuilder::{ExpressionBuilder};


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
            CheckPred(f) => {
                let tv = ex.trueval.unwrap();
                let fv = ex.falseval.unwrap();
                let res = ex.exec_function(*f,vec![input,output]);
                if res==tv {true}
                else if res==fv {false}
                else {panic!()}
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
    pub fn refine(&mut self,a:usize,lit:RefineLiteral)->bool {
        match self {
            JustIO(w) => w.refine(a,lit),
            _=>panic!("not supported yet!")
        }
    }
    pub fn refine_disjoint(&mut self,lits:Vec<(usize,RefineLiteral)>)->bool {
        match self {
            JustIO(w) => w.refine_disjoint(lits),
            _=>panic!("not supported yet!")
        }
    }
    pub fn get_next(&mut self) -> Option<HashMap<usize,BaseLiteral>> {
        match self {
            JustIO(w) => w.get_next(),
            _=>panic!("not supported yet!")
        }
    }
    pub fn increment(&mut self) -> bool {
        match self {
            JustIO(w) => w.increment(),
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



#[derive(Clone)]
pub enum RefineLiteral {
    EqLit(usize),
    NeqLit(usize)
}
use RefineLiteral::{*};
impl RefineLiteral {
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
#[derive(Clone)]
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


#[derive(Clone)]
pub struct Spec {
    i:Cluster<usize>,
    f_to_disj:Graph<usize,usize,RefineLiteral>,//f(x),  disj[],  literal,  (and edge index is available)
    implication:Graph<usize,(usize,usize),()>,//f_to_disj[edge],  (disj[], f_to_disj[edge])
    trueset:HashMap<usize,BaseLiteral>
}
impl Spec {
    pub fn new()->Self {
        Spec {
            i:Cluster::new(),
            f_to_disj:Graph::new(),
            implication:Graph::new(),
            trueset:HashMap::new()
        }
    }
    pub fn refine(&mut self,a:usize,lit:RefineLiteral)->bool {
        let mut queue = VecDeque::new();
        queue.push_back((a,lit));
        while let Some((a,lit)) = queue.pop_front() {
            match self.trueset.entry(a) {
                Occupied(mut x)=>{if !x.get_mut().intersect(&lit) {return false}}
                Vacant(x)=>{x.insert(BaseLiteral::from(&lit));}
            }
            let we = self.f_to_disj.iter_a(a).map(|(x,z,y)|(x.clone(),z,y)).collect::<Vec<_>>().into_iter();
            for (lit2,l1,clu) in we {
                if lit.implies(&lit2) {
                    for (_,l2,_) in self.f_to_disj.remove_b(clu) {
                        self.implication.remove_a(l2).for_each(drop);
                        self.implication.remove_b((clu,l2)).for_each(drop);
                    }
                    self.i.remove(clu);
                }
                if lit.conflicts(&lit2) {
                    self.implication.remove_a(l1).for_each(drop);//some of these removes are redundant but figuring out which ones is very difficult.
                    self.implication.remove_b((clu,l1)).for_each(drop);
                    let GraphBox {top,down,right,..} = self.f_to_disj.remove_direct_with_links(l1);
                    if let (None,Some(x))|(Some(x),None) = (top,down) {
                        let GraphBox {top,down,a:a2,..} = self.f_to_disj.get_direct_with_links(x);
                        let a2=*a2;//redeclare to dereference early so as to appease the borrow checker
                        if let (None,None)=(top,down) {//this is a stupid way to check if only one element remains.
                            self.implication.remove_a(x).for_each(drop);
                            self.implication.remove_b((clu,x)).for_each(drop);
                            let lit3 = self.f_to_disj.remove_direct(x);
                            self.i.remove(clu);
                            queue.push_back((a2,lit3));
                            continue;
                        }
                    }
                    if *self.i.get(clu)==l1 {
                        for (mo,ind) in self.i.iter_mut_from(self.i.next(clu)) {
                            *mo = self.f_to_disj.first_b(ind).unwrap();
                        }
                        match right {
                            Some(right) => {*self.i.get_mut(clu) = right;}
                            None => {
                                *self.i.get_mut(clu) = self.f_to_disj.first_b(clu).unwrap();
                                let mut rewr = self.i.prev(clu);
                                while let Some(r) = rewr {
                                    match self.f_to_disj.direct_next_b(*self.i.get(r)) {
                                        Some(x) => {
                                            *self.i.get_mut(r) = x;
                                            return true;
                                        }
                                        None => {
                                            *self.i.get_mut(r) = self.f_to_disj.first_b(r).unwrap();
                                            rewr = self.i.prev(r);
                                        }
                                    }
                                }
                                return false;
                            }
                        }
                    }
                }
            }
        } true
    }
    pub fn get_next(&mut self) -> Option<HashMap<usize,BaseLiteral>> {
        let mut truthset : HashMap<usize,BaseLiteral> = self.trueset.clone();
        let mut ind = self.i.first();
        let mut changestack : Vec<(usize,Option<BaseLiteral>,Vec<usize>)> = Vec::new();
        let mut overriderows : HashSet<usize> = HashSet::new();
        let mut previouschoices : HashMap<usize,usize> = HashMap::new();
        while let Some(i)=ind {
            if overriderows.contains(&i) {continue;}
            let slot = *self.i.get(i);
            let mut added : Vec<usize> = Vec::new();
            let mut skipping = false;
            for (_,_,(skrow,specific_edge)) in self.implication.iter_a(slot) {
                let pch = previouschoices.get(&skrow).copied();
                if Some(specific_edge) == pch {
                    for j in take(&mut added).into_iter() {overriderows.remove(&j);}
                    skipping=true;
                    break;
                }
                if None == pch {
                    if overriderows.insert(i) {added.push(i);}
                }
            }
            if !skipping {
                let GraphBox {e:lit,a,..} = self.f_to_disj.get_direct_with_links(slot);
                let lit=lit.clone().unwrap();let a=*a;
                let prev = match truthset.entry(a) {
                    Occupied(mut x)=>{
                        let y = x.get().clone();
                        if !x.get_mut().intersect(&lit) {
                            skipping = true;
                        } Some(y)
                    }
                    Vacant(x)=>{x.insert(BaseLiteral::from(&lit));None}
                };
                if !skipping {
                    changestack.push((a,prev,added));
                    previouschoices.insert(i,slot);
                    ind = self.i.next(i);
                    continue;
                }
            }
            for j in added.iter() {overriderows.remove(&j);}
            for (mo,ind) in self.i.iter_mut_from(self.i.next(i)) {
                *mo = self.f_to_disj.first_b(ind).unwrap();
            }
            while let Some(i)=ind {
                match self.f_to_disj.direct_next_b(*self.i.get(i)) {
                    Some(x) => {
                        *self.i.get_mut(i) = x;
                        break;
                    }
                    None => {
                        *self.i.get_mut(i) = self.f_to_disj.first_b(i).unwrap();
                        ind = self.i.prev(i);
                        let (ra,rlit,radd) = changestack.pop().unwrap();
                        if let Some(ii) = ind {previouschoices.remove(&ii);}
                        for j in radd.iter() {overriderows.remove(&j);}
                        match rlit {
                            Some(rlit) => {truthset.insert(ra,rlit);}
                            None => {truthset.remove(&ra);}
                        }
                    }
                }
            }
            return None
        } Some(truthset)
    }
    pub fn increment(&mut self) -> bool {
        let mut ind = self.i.last();
        while let Some(i)=ind {
            match self.f_to_disj.direct_next_b(*self.i.get(i)) {
                Some(x) => {
                    *self.i.get_mut(i) = x;
                    return true;
                }
                None => {
                    *self.i.get_mut(i) = self.f_to_disj.first_b(i).unwrap();
                    ind = self.i.prev(i);
                }
            }
        } false
    }
    pub fn refine_disjoint(&mut self,mut lits:Vec<(usize,RefineLiteral)>)->bool {
        let mut encount = 0;
        let mut l_i = 0;
        let mut remv = Vec::new();
        for (i,(a,lit)) in lits.iter().enumerate() {
            if let Some(x) = self.trueset.get(&a) {
                if x.implies(&lit) {return true;}
                if x.conflicts(&lit) {remv.push(i);continue;}
                l_i=i;encount+=1;
            }
        }
        if encount==0 {return false}
        if encount==1 {let (a,lit) = lits.remove(l_i);return self.refine(a,lit);}
        while let Some(x) = remv.pop() {lits.swap_remove(x);}
        let i = self.i.preempt_spot();
        let mut first_dedup = HashSet::new();
        let mut crawler = 0;
        //each new edge can only imply one thing from a given row, nothing else is worth tracking.
        for (a,lit) in lits.into_iter() {
            let nedge = self.f_to_disj.preempt_spot();
            let mut second_dedup = HashSet::new();
            for (lit2,edge,oclu) in self.f_to_disj.iter_a(a) {
                if lit2.implies(&lit) && !first_dedup.contains(&edge) {
                    first_dedup.insert(edge);
                    self.implication.insert(edge,(i,nedge),());
                }
                if lit.implies(lit2) && !second_dedup.contains(&oclu) {
                    second_dedup.insert(oclu);
                    self.implication.insert(nedge,(oclu,edge),());
                }
            }
            crawler = self.f_to_disj.insert(a,i,lit);
        }
        self.i.insert(crawler); true
    }
}


