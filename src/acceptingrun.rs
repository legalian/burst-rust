


use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::iter::{*};
use crate::ntfa::{*};
use crate::dsl::{*};
use crate::nftabuilder::{*};
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};
use Transition::{*};

#[derive(Debug)]
enum Assignment {
    Join(Rc<Assignment>,Rc<Assignment>),
    More(Rc<Assignment>,usize,usize),
    Just(usize,usize)
}
use Assignment::{*};
struct AssignmentIterator<'a> {
    s:Option<&'a Assignment>,
    backlog:Vec<&'a Assignment>
}
impl Assignment {
    fn iter(&self) -> impl Iterator<Item=(usize,usize)> + '_ {
        AssignmentIterator {
            s:Some(self),
            backlog:Vec::new()
        }
    }
    fn get(&self,a:usize)->Option<usize> {
        for (j,k) in self.iter() {
            if j==a {return Some(k)}
        } None
    }
}
fn tovec(a:&Option<Rc<Assignment>>) -> Vec<(usize,usize)> {
    match a {
        None=>Vec::new(),
        Some(z)=>{
            let mut k : Vec<_> = z.iter().collect();
            k.sort_unstable();
            k.dedup();
            k
        }
    }
}
fn subset(a:&Option<Rc<Assignment>>,b:&Option<Rc<Assignment>>) -> bool {
    if let Some(z)=a {//inserting subset of present
        if let Some(xx)=b {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
        else {false}
    } else {true}
}
impl<'a> Iterator for AssignmentIterator<'a> {
    type Item = (usize,usize);
    fn next(&mut self)->Option<(usize,usize)> {
        loop {
            match self.s {
                None=>{return None;}
                Some(Just(k,b))=>{
                    self.s=self.backlog.pop();
                    return Some((*k,*b));
                }
                Some(More(p,k,b))=>{
                    self.s=Some(p);
                    return Some((*k,*b));
                }
                Some(Join(p,j))=>{
                    self.backlog.push(p);
                    self.s=Some(j);
                }
            }
        }
    }
}
fn nondisjoint_assignment_union(a:Option<Rc<Assignment>>,b:Option<Rc<Assignment>>) -> Option<Rc<Assignment>> {
    match (a,b) {
        (None,b)|(b,None)=>b,
        (Some(a),Some(b))=>Some(Rc::new(Join(a,b)))
    }
}
fn disjoint_assignment_union(a:Option<Rc<Assignment>>,b:Option<Rc<Assignment>>) -> Option<Option<Rc<Assignment>>> {
    match (a,b) {
        (None,b)|(b,None)=>Some(b),
        (Some(a),Some(b))=>{
            for (ak,ac) in a.iter() {
                for (bk,bc) in b.iter() {
                    if ak == bk && ac != bc {return None;}
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


impl NTFABuilder {

    pub fn get_boring_accepting_run(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder
    ) -> (Dsl,usize,Vec<(usize,usize)>) {
        let mut queue : BinaryHeap<SolutionStatusWrap> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Rc<SolutionStatus>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus>>,Transition,usize,usize)> = Vec::new();
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
        let SolutionStatus {dsl:a,size:b,mapping:c,..} = &*solns.remove(&start).unwrap();
        (a.clone(),*b,tovec(c))
    }



    pub fn get_accepting_runs(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder
    ) -> Vec<(Dsl,usize,Vec<(usize,usize)>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus>>,Transition,usize,usize)> = Vec::new();
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
                    let sol = match sol.insert(solns.entry(x).or_default()) {None=>{continue;},Some(x)=>x};
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
        solns.remove(&start).unwrap_or_default().into_iter().map(|x|{
            let SolutionStatus{dsl:a,size:b,mapping:c,..} = &*x;
            (a.clone(),*b,tovec(c))
        }).collect()
    }
}


#[derive(Clone,Debug)]
struct SolutionStatus {
    dsl:Dsl,
    size:usize,
    mapping:Option<Rc<Assignment>>,
    node:usize
}
#[derive(Debug)]
struct SolutionStatusWrap(usize,usize,Option<SolutionStatus>);
impl Eq for SolutionStatusWrap {}
impl Ord for SolutionStatusWrap {
    fn cmp(&self, other: &Self) -> Ordering {other.1.cmp(&self.1)}
}
impl PartialOrd for SolutionStatusWrap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {Some(other.1.cmp(&self.1))}
}
impl PartialEq<SolutionStatusWrap> for SolutionStatusWrap {
    fn eq(&self, other: &Self) -> bool {self.1 == other.1}
}

impl SolutionStatus {
    fn compare_usefulness(&self,other:&SolutionStatus)->Ordering {
        let SolutionStatus{size:s,mapping:m,..} = other;
        match (subset(m,&self.mapping),subset(&self.mapping,m),self.size.cmp(s)) {
            (true,_,Greater|Equal)=>Less,
            (_,true,Less|Equal)=>Greater,
            _=>Equal
        }
    }
    fn insert(self,l:&mut Vec<Rc<SolutionStatus>>) -> Option<&mut Rc<SolutionStatus>> {
        let mut j = 0;
        loop {
            if j==l.len() {l.push(Rc::new(self));return l.last_mut();}
            match self.compare_usefulness(&l[j]) {
                Less=>{return None;}
                Greater=>{l.remove(j);}
                Equal=>{j+=1;}
            }
        }
    }
    fn absolute_carry(
        a:Transition,
        v:&Vec<Rc<SolutionStatus>>,
        builder:&mut ExpressionBuilder,
        ntfa:&NTFABuilder,
        x:usize
    )->SolutionStatus {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        // let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mut mapping = v.iter().fold(None,|a,x|nondisjoint_assignment_union(a,x.mapping.clone()));
        if let Recursion=a {
            let mut inp = ntfa.paths[v[0].node].2.clone();
            let oup = &ntfa.paths[x].2;
            while let Some((f,_)) = inp.first().copied() {
                let mut ins = Vec::new();
                inp.retain(|(z,(a,_))|if *z==f {ins.push(*a);false} else {true});
                // if ins.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                let outs : Vec<_> = oup.iter().filter(|(z,_)|*z==f).map(|(_,(z,_))|*z).collect();
                // if outs.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                mapping=Some(Rc::new(match mapping {
                    None=>Just(ins[0],outs[0]),
                    Some(x)=>More(x,ins[0],outs[0])
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
        v:&Vec<Rc<SolutionStatus>>,
        builder:&mut ExpressionBuilder,
        ntfa:&NTFABuilder,
        x:usize
    )->Option<SolutionStatus> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        // let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mut mapping = match v.iter().fold(Some(None),|a,x|match a {
            None=>None,
            Some(a)=>disjoint_assignment_union(a,x.mapping.clone())
        }) {
            Some(a)=>a,
            None=>{return None;}
        };
        if let Recursion=a {
            let mut inp = ntfa.paths[v[0].node].2.clone();
            let oup = &ntfa.paths[x].2;
            while let Some((f,_)) = inp.first().copied() {
                let mut ins = Vec::new();
                inp.retain(|(z,(a,_))|if *z==f {ins.push(*a);false} else {true});
                // if ins.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                let outs : Vec<_> = oup.iter().filter(|(z,_)|*z==f).map(|(_,(z,_))|*z).collect();
                // if outs.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                mapping=Some(Rc::new(match mapping {
                    None=>Just(ins[0],outs[0]),
                    Some(x)=>{
                        if let Some(u) = x.get(ins[0]) {
                            if u != outs[0] {return None}
                        }
                        More(x,ins[0],outs[0])
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




