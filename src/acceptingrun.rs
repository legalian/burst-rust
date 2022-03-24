


use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::iter::{*};
use crate::nfta::{*};
use crate::dsl::{*};
use crate::nftabuilder::{*};
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};
use Transition::{*};

pub trait SpecLike:Sized+Clone+Eq+Ord {
    fn get_narrow(&self) -> Option<usize>;
    fn moregeneral(&self,other:&Self,builder:&mut ExpressionBuilder)->bool;
    fn intersection(&self,other:&Self,builder:&mut ExpressionBuilder)->Option<Self>;
}
impl SpecLike for usize {
    fn get_narrow(&self) -> Option<usize> {Some(*self)}
    fn moregeneral(&self,other:&Self,_builder:&mut ExpressionBuilder)->bool {self==other}
    fn intersection(&self,other:&Self,_builder:&mut ExpressionBuilder)->Option<Self> {
        if self==other {Some(*self)} else {None}
    }
}

// "each assignment you contain can also be nested inside an assignment in the other"


#[derive(Debug)]
enum Assignment<L:SpecLike> {
    Join(Rc<Assignment<L>>,Rc<Assignment<L>>),
    More(Rc<Assignment<L>>,L,L),
    Just(L,L)
}
use Assignment::{*};
struct AssignmentIterator<'a,L:SpecLike> {
    s:Option<&'a Assignment<L>>,
    backlog:Vec<&'a Assignment<L>>
}
impl<L:SpecLike> Assignment<L> {
    fn iter<'a>(&'a self) -> impl Iterator<Item=(&'a L,&'a L)> + '_ {
        AssignmentIterator {
            s:Some(self),
            backlog:Vec::new()
        }
    }
    fn getnarrow(&self,a:usize,builder:&mut ExpressionBuilder)->Option<L> {
        let mut res = None;
        for (j,k) in self.iter() {
            if j.get_narrow()==Some(a) {res=match res {
                None=>Some(k.clone()),
                Some(k2)=>Some(k2.intersection(&k,builder).unwrap())
            }}
        } res
    }
}
fn tovec<L:SpecLike>(a:&Option<Rc<Assignment<L>>>) -> Vec<(L,L)> {
    match a {
        None=>Vec::new(),
        Some(z)=>{
            let mut k : Vec<_> = z.iter().map(|(a,b)|(a.clone(),b.clone())).collect();
            k.sort_unstable();
            k.dedup();
            k
        }
    }
}
fn subset<L:SpecLike>(a:&Option<Rc<Assignment<L>>>,b:&Option<Rc<Assignment<L>>>,builder:&mut ExpressionBuilder) -> bool {
    if let Some(z)=a {//inserting subset of present
        if let Some(xx)=b {z.iter().all(|(k,v)|{
            xx.iter().any(|(k2,v2)|k.moregeneral(k2,builder)&&v2.moregeneral(v,builder))
        })} else {false}
    } else {true}
}
impl<'a,L:SpecLike> Iterator for AssignmentIterator<'a,L> {
    type Item = (&'a L,&'a L);
    fn next(&mut self)->Option<(&'a L,&'a L)> {
        loop {
            match self.s {
                None=>{return None;}
                Some(Just(k,b))=>{
                    self.s=self.backlog.pop();
                    return Some((k,b));
                }
                Some(More(p,k,b))=>{
                    self.s=Some(p);
                    return Some((k,b));
                }
                Some(Join(p,j))=>{
                    self.backlog.push(p);
                    self.s=Some(j);
                }
            }
        }
    }
}
fn nondisjoint_assignment_union<L:SpecLike>(a:Option<Rc<Assignment<L>>>,b:Option<Rc<Assignment<L>>>) -> Option<Rc<Assignment<L>>> {
    match (a,b) {
        (None,b)|(b,None)=>b,
        (Some(a),Some(b))=>Some(Rc::new(Join(a,b)))
    }
}
fn disjoint_assignment_union<L:SpecLike>(a:Option<Rc<Assignment<L>>>,b:Option<Rc<Assignment<L>>>,builder:&mut ExpressionBuilder) -> Option<Option<Rc<Assignment<L>>>> {
    match (a,b) {
        (None,b)|(b,None)=>Some(b),
        (Some(a),Some(b))=>{
            for (ak,ac) in a.iter() {
                if let Some(z) = ak.get_narrow() {
                    if let Some(w) = b.getnarrow(z,builder) {
                        if ac.intersection(&w,builder).is_none() {
                            return None;
                        }
                    }
                }
            }
            Some(Some(Rc::new(Join(a,b))))
        }
    }
}

fn disjoint_union(mut a:HashMap<usize,usize>,b:HashMap<usize,usize>) -> Option<HashMap<usize,usize>> {
    for (k,v) in b.into_iter() {
        match a.entry(k) {
            Vacant(hole) => {hole.insert(v);}
            Occupied(spot) => {
                if *spot.get() != v {return None;}
            }
        }
    } Some(a)
}


impl<L:SpecLike> NFTABuilder<L> {
    pub fn get_boring_accepting_run(
        &self,
        start:Vec<usize>,
        builder:&mut ExpressionBuilder
    ) -> (Dsl,usize,Vec<(L,L)>) {
        let mut queue : BinaryHeap<SolutionStatusWrap<L>> = BinaryHeap::new();
        for s in start.iter() {
            queue.push(SolutionStatusWrap(*s,0,None));
        }
        let mut solns : HashMap<usize,Rc<SolutionStatus<L>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus<L>>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus<L>>>,Transition,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x].0;
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        let sol = SolutionStatus::absolute_carry(*f,&vec![],builder,self,x);
                        queue.push(SolutionStatusWrap(x,minsize+sol.size,Some(sol)));
                    } else {
                        for (f,l) in y.iter() {
                            if l.contains(&x) {continue;}
                            stack.push((l,Vec::new(),*f,x,minsize));
                        }
                    }
                }
                Some(sol)=>{
                    if start.contains(&x) {
                        let SolutionStatus {dsl:a,size:b,mapping:c,..} = sol;
                        return (a,b,tovec(&c));
                    }
                    let sol = match solns.entry(x) {
                        Occupied(_)=>{continue;}
                        Vacant(y)=>{y.insert(Rc::new(sol))}
                    };
                    for (l,mut v,f,y,minsize) in working.remove(&x).into_iter().flatten() {
                        v.push(sol.clone());
                        stack.push((l,v,f,y,minsize+sol.size));
                    }
                }
            }
            while let Some((l,mut v,f,x,minsize)) = stack.pop() {
                if l.len()==0 {
                    let sol = SolutionStatus::absolute_carry(f,&v,builder,self,x);
                    queue.push(SolutionStatusWrap(x,minsize,Some(sol)));
                    continue;
                }
                match solns.get(&l[0]) {
                    None=>{
                        queue.push(SolutionStatusWrap(l[0],minsize,None));
                        working.entry(l[0]).or_default().push((&l[1..],v,f,x,minsize));
                    }
                    Some(sol)=>{
                        v.push(sol.clone());
                        stack.push((&l[1..],v,f,x,minsize+sol.size));
                    }
                }
            }
        }
        panic!("no solution!");
    }



    pub fn get_accepting_runs(
        &self,
        start:Vec<usize>,
        builder:&mut ExpressionBuilder
    ) -> Vec<(Dsl,usize,Vec<(L,L)>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap<L>> = BinaryHeap::new();
        for s in start.iter() {
            queue.push(SolutionStatusWrap(*s,0,None));
        }
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus<L>>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus<L>>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus<L>>>,Transition,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x].0;
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        // println!("found nullary!");
                        for sol in SolutionStatus::optional_carry(*f,&vec![],builder,self,x) {
                            queue.push(SolutionStatusWrap(x,minsize+sol.size,Some(sol)));
                        }
                    } else {
                        for (f,l) in y.iter() {
                            if l.contains(&x) {continue;}
                            stack.push((l,Vec::new(),*f,x,1+minsize));
                        }
                    }
                }
                Some(sol)=>{
                    let sol = match sol.insert(solns.entry(x).or_default(),builder) {None=>{continue;},Some(x)=>x};
                    for (l,v,f,y,minsize) in working.get(&x).into_iter().flatten() {
                        let mut v2=v.clone();
                        v2.push(sol.clone());
                        stack.push((l,v2,*f,*y,minsize+sol.size));
                    }
                }
            }
            while let Some((l,v,f,x,minsize)) = stack.pop() {
                if l.len()==0 {
                    for sol in SolutionStatus::optional_carry(f,&v,builder,self,x) {
                        queue.push(SolutionStatusWrap(x,minsize,Some(sol)));
                    }
                    continue;
                }
                queue.push(SolutionStatusWrap(l[0],minsize,None));
                for sol in solns.get(&l[0]).into_iter().flatten().cloned() {
                    let mut v2=v.clone();
                    let msz = minsize+sol.size;
                    v2.push(sol);
                    stack.push((&l[1..],v2,f,x,msz));
                }
                working.entry(l[0]).or_default().push((&l[1..],v,f,x,minsize));
            }
        }
        let mut result = Vec::new();
        for s in start.iter() {
            if let Some(z) = solns.remove(&s) {
                for x in z {
                    (*x).clone().insert(&mut result,builder);
                }
            }
        }
        result.into_iter().map(|x|{
            let SolutionStatus{dsl:a,size:b,mapping:c,..} = &*x;
            (a.clone(),*b,tovec(c))
        }).collect()
    }
}


#[derive(Clone,Debug)]
struct SolutionStatus<L:SpecLike> {
    dsl:Dsl,
    size:usize,
    mapping:Option<Rc<Assignment<L>>>,
    node:usize
}
#[derive(Debug)]
struct SolutionStatusWrap<L:SpecLike>(usize,usize,Option<SolutionStatus<L>>);
impl<L:SpecLike> Eq for SolutionStatusWrap<L> {}
impl<L:SpecLike> Ord for SolutionStatusWrap<L> {
    fn cmp(&self, other: &Self) -> Ordering {other.1.cmp(&self.1)}
}
impl<L:SpecLike> PartialOrd for SolutionStatusWrap<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {Some(other.1.cmp(&self.1))}
}
impl<L:SpecLike> PartialEq<SolutionStatusWrap<L>> for SolutionStatusWrap<L> {
    fn eq(&self, other: &Self) -> bool {self.1 == other.1}
}

impl<L:SpecLike> SolutionStatus<L> {
    fn compare_usefulness(&self,other:&SolutionStatus<L>,builder:&mut ExpressionBuilder)->Ordering {
        let SolutionStatus{size:s,mapping:m,..} = other;
        match (subset(m,&self.mapping,builder),subset(&self.mapping,m,builder),self.size.cmp(s)) {
            (true,_,Greater|Equal)=>Less,
            (_,true,Less|Equal)=>Greater,
            _=>Equal
        }
    }
    fn insert<'a>(self,l:&'a mut Vec<Rc<SolutionStatus<L>>>,builder:&mut ExpressionBuilder) -> Option<&'a mut Rc<SolutionStatus<L>>> {
        let mut j = 0;
        loop {
            if j==l.len() {l.push(Rc::new(self));return l.last_mut();}
            match self.compare_usefulness(&l[j],builder) {
                Less=>{return None;}
                Greater=>{l.remove(j);}
                Equal=>{j+=1;}
            }
        }
    }
    fn absolute_carry(
        a:Transition,
        v:&Vec<Rc<SolutionStatus<L>>>,
        builder:&mut ExpressionBuilder,
        nfta:&NFTABuilder<L>,
        x:usize
    )->SolutionStatus<L> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        // let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mut mapping = v.iter().fold(None,|a,x|nondisjoint_assignment_union(a,x.mapping.clone()));
        if let Recursion=a {
            let oup = &nfta.paths[x].2;
            for (f,in_l) in nfta.paths[v[0].node].2.iter() {
                let out_l = match oup.iter().find(|(z,_)|z==f){
                    None=>{continue;}
                    Some((_,z))=>z
                };
                mapping=Some(Rc::new(match mapping {
                    None=>Just(in_l.clone(),out_l.clone()),
                    Some(x)=>More(x,in_l.clone(),out_l.clone())
                }));
            }
        }
        let mut v = v.iter().map(|x|x.dsl.clone()).collect::<Vec<_>>();
        let dsl = match a {
            Constant(x)=>BaseValue(x),
            ArbitraryFunc(w)=>ApplyStack(Box::new(BaseValue(builder.functions[w].concval)),v),
            Recursion=>ApplyStack(Box::new(RecursivePlaceholder),v),
            Switch(_)=>SwitchValue(Box::new(v.remove(0)),v),
            Input=>AccessStack(0),
            Transition::Construct(x)=>Dsl::Construct(x,v),
            Destruct(x,y)=>Deconstruct(x,y,Box::new(v.remove(0))),
        };
        SolutionStatus {
            dsl,size,mapping,node:x
        }
    }

    fn optional_carry(
        a:Transition,
        v:&Vec<Rc<SolutionStatus<L>>>,
        builder:&mut ExpressionBuilder,
        nfta:&NFTABuilder<L>,
        x:usize
    )->Option<SolutionStatus<L>> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        // let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mut mapping = match v.iter().fold(Some(None),|a,x|match a {
            None=>None,
            Some(a)=>disjoint_assignment_union(a,x.mapping.clone(),builder)
        }) {
            Some(a)=>a,
            None=>{return None;}
        };
        if let Recursion=a {
            let oup = &nfta.paths[v[0].node].2;
            for (f,out_l) in nfta.paths[x].2.iter() {
                let in_l = match oup.iter().find(|(z,_)|z==f){
                    None=>{continue;}
                    Some((_,z))=>z
                };
                mapping=Some(Rc::new(match mapping {
                    None=>Just(in_l.clone(),out_l.clone()),
                    Some(x)=>{
                        if let Some(in_s) = in_l.get_narrow() {
                            if let Some(u) = x.getnarrow(in_s,builder) {
                                if u.intersection(out_l,builder).is_none() {return None}
                            }
                        }
                        More(x,in_l.clone(),out_l.clone())
                    }
                }));
            }
        }
        let mut v = v.iter().map(|x|x.dsl.clone()).collect::<Vec<_>>();
        let dsl = match a {
            Constant(x)=>BaseValue(x),
            ArbitraryFunc(w)=>ApplyStack(Box::new(BaseValue(builder.functions[w].concval)),v),
            Recursion=>ApplyStack(Box::new(RecursivePlaceholder),v),
            Switch(_)=>SwitchValue(Box::new(v.remove(0)),v),
            Input=>AccessStack(0),
            Transition::Construct(x)=>Dsl::Construct(x,v),
            Destruct(x,y)=>Deconstruct(x,y,Box::new(v.remove(0))),
        };
        Some(SolutionStatus {
            dsl,size,mapping,node:x
        })
    }

}




