
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::hash_map::Entry::*;
use std::iter::once;

struct Expr {
    handle:usize,
    args:Vec<Expr>
}

struct NTFA {
    nullary:HashMap<usize,usize>,
    rules:HashMap<usize,HashMap<usize,Vec<Vec<usize>>>>,
    accepting_states:HashSet<usize>
}
//invariants: all 0-ary rules are at the beginning of the rules list, and appear in sorted order by their ids.
//also the left hand side of rules are always unique
//then there's the obvious invariants, like the index, and how it needs to have a slot for every state, and how
//  each entry of the index contains a map to all of that variable's occurences in the rule parameters,
//  and also how the hashmaps in the index shouldn't have any entry corresponding to an empty vec.

struct SolutionSearchProblem<'a> {
    nullary : HashMap<usize,Vec<usize>>,
    totalset : HashMap<usize,Vec<(usize,&'a [usize],usize,usize)>>,//final:(a0,an,f,index)
    queue : VecDeque<usize>
}
// enum SolutionSearch<'a> {
//     Found(Expr),
//     Searching(
//         Vec<(usize,&'a [usize],usize,usize)>,
//         Vec<usize>,
//         Vec<Option<(usize,usize)>>
//     )
// }
// use SolutionSearch::{*};
impl<'a> SolutionSearchProblem<'a> {
    fn enqueueFinalStates(&mut self,ntfa:&NTFA) {
        for state in ntfa.accepting_states {
            self.queue.push_back(state);
        }
    }
    fn add_nullary(&mut self,f:usize,r:usize) {
        self.nullary.entry(r).or_default().push(f);
    }
    fn add(&mut self,a0:usize,an:&'a [usize],f:usize,index:usize) {
        self.totalset.entry(an[an.len()-1]).or_default().push((a0,an,f,index));
    }
    fn addNTFA(&mut self,ntfa:&'a NTFA) {
        for (f,r) in ntfa.nullary.iter() {
            self.add_nullary(*f,*r);
        }
        for (a0,rest1) in ntfa.rules.iter() {
            for (f,rest2) in rest1.iter() {
                for (i,an) in rest2.iter().enumerate() {
                    self.add(*a0,an,*f,i);
                }
            }
        }
    }
    // fn depleteQueueGetSolution(&mut self) {
    //     let gov:HashMap<usize,SolutionSearch> = HashMap::new();
    //     while let Some(x) = self.queue.pop_front() {
    //         match (self.nullary.remove(&x),self.totalset.remove(&x)) {
    //             (Some(y),_)=>{gov.insert(x,Found(Expr{handle:y[0],args:vec![]}));}
    //             (_,Some(y))=>{
    //                 gov.insert(x,Searching(
    //                     y,
    //                     ,

    //                 ));
    //             }
    //         }
    //         if let Some(y) = self.totalset.remove(&x) {
    //             for (a0,an,f,index) in y {
    //                 self.queue.push_back(a0);
    //                 for a in an {self.queue.push_back(*a);}
    //             }
    //         }
    //     }
    // }
    fn depleteQueue(&mut self) {
        while let Some(x) = self.queue.pop_front() {
            self.nullary.remove(&x);
            if let Some(y) = self.totalset.remove(&x) {
                for (a0,an,f,index) in y {
                    self.queue.push_back(a0);
                    for a in an {self.queue.push_back(*a);}
                }
            }
        }
    }
    fn refineNTFA(&self,ntfa:&mut NTFA) {
        for (_,removals) in self.nullary {
            for r in removals {
                ntfa.nullary.remove(&r);
            }
        }
        for (_,removals) in self.totalset {
            for (a0,an,f,index) in removals.iter().rev() {//index is always in increasing order as it occurs in removals
                ntfa.rules[a0][f].swap_remove(*index);
            }//but not after this is finished. so calling refine more than once in a row with the same object is undefined behavior.
        }
    }
}


struct IntersectionProblem<'a> {
    a : &'a NTFA,
    b : &'a NTFA,
    queue : VecDeque<(usize,usize,usize)>,
    a_to_b : HashMap<usize,HashMap<usize,usize>>,
    b_to_c : HashMap<usize,HashMap<(usize,Vec<usize>),Vec<&'a [usize]>>>,
    c_to_a : HashMap<(usize,Vec<usize>),HashMap<usize,Vec<&'a [usize]>>>,
    states : usize,
    result : NTFA
}
impl<'a> IntersectionProblem<'a> {
    fn new(a:&'a NTFA,b:&'a NTFA)->IntersectionProblem<'a> {
        IntersectionProblem {
            a,b,queue:VecDeque::new(),
            a_to_b:HashMap::new(),b_to_c:HashMap::new(),c_to_a:HashMap::new(),
            result:NTFA {
                nullary:HashMap::new(),rules:HashMap::new(),accepting_states:HashSet::new()
            },
            states:0
        }
    }
    fn populate_queue(&mut self) {
        for (k,va) in self.a.nullary.iter() {
            if let Some(vb) = self.b.nullary.get(&k) {
                let newvar = self.get_variable(*va,*vb);
                self.result.nullary.insert(*k,newvar);
            }
        }
    }
    fn get_variable(&mut self,a:usize,b:usize)->usize {
        match self.a_to_b.entry(a).or_insert(HashMap::new()).entry(b) {
            Occupied(x)=>*x.get(),
            Vacant(x)=>{
                if self.a.accepting_states.contains(&a) && self.b.accepting_states.contains(&b) {
                    self.result.accepting_states.insert(self.states);
                }
                self.queue.push_back((a,b,self.states));
                x.insert(self.states);
                self.states+=1;
                self.states-1
            }
        }
    }
    fn cosolve(mut self,av:&[&[usize]],bv:&[&[usize]],cf:usize,newnvarnvec:Vec<usize>) {
        if av[0].len()==1 {
            let newvarname = self.get_variable(av[0][0],bv[0][0]);
            self.result.rules.entry(newnvarnvec[0]).or_default().entry(cf).or_default().push(
                newnvarnvec.iter().skip(1).cloned().chain(once(newvarname)).collect()
            );
            return
        }
        let mut innerqueue : VecDeque<(&[&[usize]],&[&[usize]],Vec<usize>)> = VecDeque::new();
        innerqueue.push_back((av,bv,newnvarnvec));
        while let Some((av,bv,newnvarnvec)) = innerqueue.pop_front() {
            if av[0].len()==1 {
                let newvarname = self.get_variable(av[0][0],bv[0][0]);
                self.result.rules.entry(newnvarnvec[0]).or_default().entry(cf).or_default().push(
                    newnvarnvec.iter().skip(1).cloned().chain(once(newvarname)).collect()
                );
                continue
            }
            let ca_line = self.c_to_a.entry((cf,newnvarnvec.clone())).or_default();
            for a in av {
                ca_line.entry(a[0]).or_default().push(&a[1..]);
                if let Some(inter_b) = self.a_to_b.get(&a[0]) {
                    for (b,newtag) in inter_b.iter() {
                        if let Some(inter_c) = self.b_to_c.get(b) {
                            if let Some(otherlines) = inter_c.get(&(cf,newnvarnvec.clone())) {
                                innerqueue.push_back((
                                    vec![&a[1..]],
                                    otherlines,
                                    newnvarnvec.iter().cloned().chain(once(*newtag)).collect()
                                ));
                            }
                        }
                    }
                }
            }
            for b in bv {
                self.b_to_c.entry(b[0]).or_default().entry((cf,newnvarnvec.clone())).or_default().push(&b[1..]);
                for (a,otherlines) in ca_line.iter() {
                    if let Some(ca_line) = self.a_to_b.get(a) {
                        if let Some(newtag) = ca_line.get(&b[0]) {
                            innerqueue.push_back((
                                otherlines,
                                vec![&b[1..]],
                                newnvarnvec.iter().cloned().chain(once(*newtag)).collect()
                            ));
                        }
                    }
                }
            }
        }
    }

    fn solve(mut self)->NTFA {
        self.populate_queue();
        while let Some((aside,bside,nvarn)) = self.queue.pop_front() {
            if let Some(inter_c) = self.b_to_c.get(&bside) {
                for (c,lines_b) in inter_c.iter() {
                    if let Some(inter_a) = self.c_to_a.get(c) {
                        if let Some(lines_a) = inter_a.get(&aside) {
                            self.cosolve(lines_a,lines_b,c.0,c.1);
                        }
                    }
                }
            }
            if let (Some(ad),Some(bd)) = (self.a.rules.get(&aside),self.b.rules.get(&bside)) {
                for (k,av) in ad {
                    if let Some(bv) = bd.get(k) {
                        if av[0].len()==1 {//len(av[0])==1 implies len(av)==1
                            let newvarname = self.get_variable(av[0][0],bv[0][0]);
                            self.result.rules.entry(nvarn).or_default().entry(*k).or_default().push(vec![newvarname]);
                        } else {
                            let av_int : Vec<&[usize]> = av.iter().map(|x|x.as_slice()).collect();
                            let bv_int : Vec<&[usize]> = bv.iter().map(|x|x.as_slice()).collect();
                            self.cosolve(&av_int,&bv_int,*k,vec![nvarn]);
                        }
                    }
                }
            }
        }
        self.result
    }
}
fn intersection(a:&NTFA,b:&NTFA) -> NTFA {IntersectionProblem::new(a,b).solve()}
impl NTFA {fn intersect(&mut self,b:&NTFA) {*self=intersection(self,b)}}


// wait a second- each rule that gets advanced is just waiting for a single variable to advance it??????????




//is it horrifyingly specific? hell yeah it is but i want to mine all the efficiency I can out of this because it's
//  the backbone of bottom up synthesis- i want it to take 0 seconds so i can focus on little optimizations to the search space.
//i'll provide debugging functions so it's a little more friendly to play around with- just to make up for the general unreadability
// fn intersection(a:&NTFA,b:&NTFA) -> NTFA {
//     let mut index = Vec::new();
//     let mut rules = Vec::new();
//     let mut assoc = HashMap::new();
//     let mut queue = VecDeque::new();
//     let mut states = 0;

//     // Vec< HashMap<(usize,usize),(bool,bool,)> >
//     // Vec<Vec< Vec<usize> >>

//     let mut a_mod_index:Vec<HashMap<(usize,usize),Vec<(Box<[usize]>,usize)>>> = Vec::new(); 
//     let mut b_mod_index:Vec<HashMap<(usize,usize),Vec<(Box<[usize]>,usize)>>> = Vec::new();
//     {
//         let mut ai=0;
//         let mut bi=0;
//         while ai<a.rules.len() && bi<b.rules.len() && a.rules[ai].1.len()==0 && b.rules[bi].1.len()==1 {
//             if      a.rules[ai].0<b.rules[bi].0 {ai+=1}
//             else if a.rules[ai].0>b.rules[bi].0 {bi+=1}
//             else {
//                 let key = (a.rules[ai].2,b.rules[bi].2);
//                 match assoc.entry(key) {
//                     Occupied(x)=>{
//                         rules.push((a.rules[ai].0,vec![],*x.get()));
//                     },
//                     Vacant(x)=>{
//                         x.insert(states);
//                         queue.push_back((key,states));
//                         index.push(HashMap::new());
//                         rules.push((a.rules[ai].0,vec![],states));
//                         states+=1;
//                     }
//                 }
//                 ai+=1;bi+=1;
//             }
//         }
//     }
//     while let Some(((aside,bside),nvarn)) = queue.pop_front() {
//         let am = &a.index[aside];
//         let bm = &b.index[bside];
//         for (k,av) in am {
//             if let Some(bv) = bm.get(k) {
//                 let cardinality = a.rules[av[0]].1.len();//av,bv contain at least one element because the entry exists
//                 if cardinality==1 {//doesn't matter which one you check the cardinality of- should be the same in each
//                     let key = (a.rules[av[0]].2,b.rules[bv[0]].2);//av,bv contain only one element if cardinality==1 because rules have unique left sides.
//                     match assoc.entry(key) {
//                         Occupied(x)=>{
//                             rules.push((*k,vec![nvarn],*x.get()));
//                         },
//                         Vacant(x)=>{
//                             x.insert(states);
//                             quh({let mut r=HashMap::new();r.insert(*k,vec![rules.len()]);r});
//                             rules.push((*k,vec![nvarn],states));
//                             states+=1;
//                         }
//                     }
//                 } else {//this part sucks
//                     // no its worse

//                     // for aw in av {
//                     //     let rule = &a.rules[*aw];
//                     //     let mut jads = vec![nvarn];
//                     //     n = 1
//                     //     while a_mod_index.len()<rule.1[n] {a_mod_index.push(HashMap::new());}
//                     //     a_mod_index[rule.1[n]].entry((rule.0,n)).or_default().push((jads.into_boxed_slice(),*aw));
//                     //     find a new var...

//                     //     jads.push(the new var);
//                     //     n+=1
//                     // }
//                     // for bw in bv {
//                     //     let rule = &b.rules[*bw];
//                     //     while b_mod_index.len()<rule.1[1] {b_mod_index.push(HashMap::new());}
//                     //     b_mod_index[rule.1[1]].entry((rule.0,1)).or_default().push((Box::new([nvarn]),*bw));
//                     // }
//                 }
//             }
//         }
//         if aside>=a_mod_index.len() || bside>=b_mod_index.len() {continue;}//I KNOW this is stupid but it makes it faster!
//         //vec access is faster than hashmap access even with this clunkyness
//         let amod = &mut a_mod_index[aside];//then youve got this other side of it; the mutable part of the index is kept separate
//         let bmod = &mut b_mod_index[bside];//because it lets you find the intersection without consuming either object.
//         //i'm actually not sure when it would be useful to take the intersection without consuming the operands, but 
//         //if it's free to use maybe i'll take advantage of it at some point for something other than the burst implementation.

//         // for (k,av) in am {
//         //     if let Some(bv) = bm.get(k) {
//         //         let cardinality = a.rules[av[0]].1.len();
//         //         if cardinality==1 {

//         //         } else {

//         //         }
//         //     }
//         // }

//     }
//     NTFA {index,rules}
// }




fn main() {
    println!("Hello, world!");
}
