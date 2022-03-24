

use std::collections::hash_map::Entry::*;
use std::mem::{take};
use std::iter::{*};
use crate::nfta::{*};
use std::cmp::{min,max};
use std::vec::IntoIter;



impl<T:Clone> NFTABuilder<T> {
    pub fn intersect(&mut self,a_side:Vec<usize>,b_side:Vec<usize>,k_limit:Option<usize>)->Vec<usize> {
        fn getmergedvl<T>(
            al:&[(Transition,Vec<usize>)],
            bl:&[(Transition,Vec<usize>)],
            paths:&[(Vec<(Transition,Vec<usize>)>,Option<usize>,Vec<(usize,T)>)],
            k_limit:Option<usize>
        )->IntoIter<(Transition,Vec<(usize,usize)>)> {
            let mut a=0;
            let mut b=0;
            let mut ao;
            let mut bo;
            let mut deps : Vec<(Transition,Vec<(usize,usize)>)> = Vec::new();
            while a<al.len() && b<bl.len() {
                if al[a].0<bl[b].0 {
                    // println!("{:?} {:?} A INC",&al[a..],&bl[b..]);
                    a+=1;
                }
                else if al[a].0>bl[b].0 {
                    // println!("{:?} {:?} B INC",&al[a..],&bl[b..]);
                    b+=1;
                }
                else {
                    let f=al[a].0;
                    ao=0;
                    bo=0;
                    while a+ao<al.len() && al[a+ao].0==f {
                        bo=0;
                        while b+bo<bl.len() && bl[b+bo].0==f {
                            if if let Some(k_limit) = k_limit {
                                al[a+ao].1.iter().zip(bl[b+bo].1.iter()).map(|(x,y)|max(paths[*x].1.unwrap(),paths[*y].1.unwrap())).sum::<usize>()+1<=k_limit
                            } else {true} {
                                deps.push((f,al[a+ao].1.iter().zip(bl[b+bo].1.iter()).map(|(x,y)|(min(*x,*y),max(*x,*y))).collect()));
                            }
                            bo+=1;
                        }
                        ao+=1;
                    }
                    a+=ao;
                    b+=bo;
                }
            }
            for (_,j) in deps.iter_mut() {j.reverse();}
            deps.into_iter()
        }
        struct ArtificialStack {
            outercollect: Vec<(Transition,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(Transition,Vec<(usize,usize)>)>,
            innertrav: Vec<(usize,usize)>,
            innertoken: Transition,
            place:usize,
            lastval:(usize,usize),
            resultant:bool
        }
        let mut stack:Vec<ArtificialStack> = Vec::new();


        let mut hook = Vec::new();
        for a_start in a_side.iter().copied() {
            for b_start in b_side.iter().copied() {
                if a_start==b_start {hook.push(a_start);continue;}
                if a_start==0 {hook.push(b_start);continue;}
                if 0==b_start {hook.push(a_start);continue;}
                let outerkey = (min(a_start,b_start),max(a_start,b_start));
                let place = match self.intersect_memo.entry(outerkey) {
                    Vacant(_) => {
                        let place = self.get_placeholder();
                        self.intersect_memo.insert(outerkey,Some(place));place
                    }
                    Occupied(z)=>{
                        if let Some(k) = z.get() {
                            hook.push(*k);
                        }
                        continue;
                    }
                };
                let mut outertrav = getmergedvl(&self.paths[a_start].0,&self.paths[b_start].0,&self.paths,k_limit);
                let (innertoken,intv) = match outertrav.next() {
                    Some(x)=>x,None=>{continue;}
                };
                stack.push(ArtificialStack{
                    outercollect:Vec::new(),
                    innercollect:Vec::new(),
                    outertrav,
                    innertoken,
                    innertrav:intv,
                    place,
                    lastval:outerkey,
                    resultant:true
                });
            }
        }

        let mut extrapass = Vec::new();
        while let Some(x) = stack.last_mut() {
            loop {
                if let Some(subl) = x.innertrav.pop() {
                    match if subl.0==0 || subl.0==subl.1 {Some(Some(subl.1))}
                        else {self.intersect_memo.get(&subl).copied()} {
                        Some(Some(y))=>{x.innercollect.push(y);continue;}
                        Some(None)=>{x.innercollect.clear();}
                        None=>{
                            let mut outertrav = getmergedvl(&self.paths[subl.0].0,&self.paths[subl.1].0,&self.paths,k_limit);
                            if let Some((innertoken,intv)) = outertrav.next() {
                                let place = self.get_placeholder();
                                extrapass.push(place);
                                self.intersect_memo.insert(subl.clone(),Some(place));
                                x.innertrav.push(subl);
                                // tracker.add_unconfirmed(place);
                                stack.push(ArtificialStack{
                                    outercollect:Vec::new(),
                                    innercollect:Vec::new(),
                                    outertrav,
                                    innertoken,
                                    innertrav:intv,
                                    place,
                                    lastval:subl,
                                    resultant:false
                                });
                                break;
                            } else {x.innercollect.clear();}
                        }
                    }
                } else {
                    let v = take(&mut x.innercollect);
                    x.outercollect.push((x.innertoken,v));
                }
                if let Some((innertoken,intv))=x.outertrav.next() {
                    x.innertoken=innertoken;
                    x.innertrav=intv;
                } else {
                    let ff = stack.pop().unwrap();
                    // tracker.depends_on(ff.place,&ff.outercollect);
                    let rpv = if ff.outercollect.len()==0 {None} else {
                        let chain = self.paths[ff.lastval.0].2.iter().cloned().chain(self.paths[ff.lastval.1].2.iter().cloned()).collect();
                        let u = self.insert_into_placeholder(ff.outercollect,ff.place,chain);
                        extrapass.push(u);
                        Some(u)
                    };
                    if rpv != Some(ff.place) {
                        self.intersect_memo.insert(ff.lastval,rpv);
                    }
                    if let Some(k) = rpv {
                        if ff.resultant {hook.push(k);}
                    }
                    break;
                }
            }
        };
        if hook.len() == 0 {return hook;}
        self.accessibility_cleaning(&extrapass,k_limit);
        hook.retain(|j|self.paths[*j].1.is_none());
        hook
    }

}
