use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_map::Entry::*;
use std::mem::{take};
use std::iter::{*};
use std::vec::IntoIter;
use std::cmp::Ordering;
use Ordering::{*};
use crate::ntfa::{*};

impl NTFABuilder {




    pub fn simplify(&mut self,accstates:Vec<usize>)->Option<usize> {
        // for a in accstates.iter() {
        //     self.purge(*a);
        // }
        if accstates.len()==0 {return None}
        if accstates.len()==1 {return Some(accstates[0])}
        let mut deps:Vec<(Transition,Vec<usize>)> = Vec::new();
        let chain : Vec<_> = accstates.iter().map(|z|self.paths[*z].2.iter().copied()).flatten().collect();
        for s in accstates {deps.extend(self.paths[s].0.iter().cloned())}
        return Some(self.get_ntfa(deps,chain));

        if accstates.len()==0 {return None}
        let mut ownership : HashMap<usize,usize> = accstates.iter().map(|x|(*x,0)).collect();
        let mut stack : Vec<usize> = accstates.clone();
        let mut nonaccstates : Vec<usize> = Vec::new();
        let mut invocc : HashMap<usize,Vec<((Transition,&[usize],&[usize]),usize)>> = HashMap::new();
        while let Some(z) = stack.pop() {
            for (f,a) in self.paths[z].0.iter() {
                for (i,c) in a.iter().copied().enumerate() {
                    if c==0 {continue;}
                    invocc.entry(c).or_default().push(((*f,&a[..i],&a[i+1..]),z));
                    match ownership.entry(c) {
                        Occupied(_)=>{},
                        Vacant(v)=>{
                            v.insert(1);
                            stack.push(c);
                            nonaccstates.push(c);
                        }
                    }
                }
            }
        }
        let mut hotpools : HashSet<usize> = HashSet::new();
        hotpools.insert(0);
        let mut pools : Vec<(Vec<usize>,Vec<usize>)> = if nonaccstates.len()==0 {
            ownership.insert(0,1);
            vec![(accstates.clone(),Vec::new()),(vec![0],Vec::new())]
        } else {
            ownership.insert(0,2);
            hotpools.insert(1);
            vec![(accstates.clone(),Vec::new()),(nonaccstates,accstates.clone()),(vec![0],Vec::new())]
        };


        // println!("-==-=--===-=-=-=-=-=-=-==--==--= begin!");
        let mut eyes : HashMap<usize,HashSet<usize>> = HashMap::new();
        let mut hotmemo : HashMap<usize,Vec<(&(Transition,&[usize],&[usize]),usize)>> = HashMap::new();
        while hotpools.len()>0 {
            let i = *hotpools.iter().next().unwrap();
            if pools[i].0.len()==1 && pools[i].1.len()==0 {
                hotpools.remove(&i);
                continue;
            }
            fn getblh<'a,'b>(
                invocc:&'a HashMap<usize,Vec<((Transition,&'a [usize],&'a [usize]),usize)>>,
                ownership:&'b HashMap<usize,usize>,
                g:usize
            )->Vec<(&'a (Transition,&'a [usize],&'a [usize]),usize)> {
                // println!("recalc: {}",g);
                let mut blh : Vec<(&(Transition,&[usize],&[usize]),usize)> = Vec::new();
                for (key,r) in invocc.get(&g).map(|g|g.iter()).into_iter().flatten() {
                    blh.push((key,ownership[r]));
                }
                blh.sort_unstable();
                blh.dedup();
                blh
            }
            fn is_superset(
                a:&[(&(Transition,&[usize],&[usize]),usize)],
                b:&[(&(Transition,&[usize],&[usize]),usize)]
            )->bool {
                if a.len()<b.len() {return false}
                let mut ia=0;let mut ib=0;
                while ia<a.len() && ib<b.len() {
                    match a[ia].cmp(&b[ib]) {
                        Less=>{ia+=1;}
                        Greater=>{return false}
                        Equal=>{ia+=1;ib+=1;}
                    }
                } !(ia==a.len() && ib<b.len())
            }
            let mut differentiator : HashMap<&[(&(Transition,&[usize],&[usize]),usize)],Vec<usize>> = HashMap::new();
            for ow in pools[i].0.iter() {
                match hotmemo.entry(*ow) { Vacant(z)=>{z.insert(getblh(&invocc,&ownership,*ow));} _=>{} }
            }
            for sub in pools[i].1.iter() {
                match hotmemo.entry(*sub) { Vacant(z)=>{z.insert(getblh(&invocc,&ownership,*sub));} _=>{} }
            }
            for ow in pools[i].0.iter() {
                differentiator.entry(&hotmemo[ow]).or_default().push(*ow);
            }

            let mut result : Vec<_> = differentiator.into_iter().map(|(a,b)|(a,b,Vec::new())).collect();
            for x in 0..result.len()-1 {
                for y in x+1..result.len() {
                    let (fst,lst) = result[x..].split_first_mut().unwrap();
                    if is_superset(fst.0,lst[y-x-1].0) {
                        lst[y-x-1].2.extend(fst.1.iter().copied());
                    }
                    if is_superset(lst[y-x-1].0,fst.0) {
                        fst.2.extend(lst[y-x-1].1.iter().copied());
                    }
                }
            }
            for sub in pools[i].1.iter() {
                let ghl = &hotmemo[sub];
                for (t,_,r) in result.iter_mut() {
                    if is_superset(ghl,t) {r.push(*sub);}
                }
            }
            
            if result.len()>1 {
                let mut result = result.into_iter();
                let ff = result.next().unwrap();
                pools[i].0 = ff.1;
                pools[i].1 = ff.2;
                for (_,v,w) in result {
                    for k in v.iter() {
                        ownership.insert(*k,pools.len());
                    }
                    hotpools.insert(pools.len());
                    pools.push((v,w));
                }
                if let Some(z) = eyes.remove(&i) {
                    for j in z {
                        hotpools.insert(j);
                    }
                }
                hotmemo.retain(|_,v|!v.iter().any(|(_,y)|*y==i));
            } else {
                let wk = result.remove(0);
                for w in wk.0 {
                    eyes.entry(w.1).or_default().insert(i);
                }
                pools[i].1 = wk.2;
                hotpools.remove(&i);
            }
        }

        // println!("\n\n{:?}\n\n",pools);
        // 'stupid: loop{{{
        //         let mut stack : Vec<usize> = accstates.clone();
        //         let mut dedup : HashSet<usize> = HashSet::new();
        //         while let Some(z) = stack.pop() {
        //             println!("{:?} := {:?}",z,self.paths[z]);
        //             for (_,a) in self.paths[z].iter() {
        //                 for c in a.iter().copied() {
        //                     if dedup.insert(c) {
        //                         stack.push(c);
        //                     }
        //                 }
        //             }
        //         }
        //         break
        // }}}
        self.apply_simplification(accstates,pools,ownership)
    }




    // fn graph_completing_simplify(&mut self)->Option<usize> {

    //     if accstates.len()==0 {return None}
    //     let mut ownership : HashMap<usize,usize> = accstates.iter().map(|x|(*x,0)).collect();
    //     let mut stack : Vec<usize> = accstates.clone();
    //     let mut nonaccstates : Vec<usize> = Vec::new();
    //     let mut invocc : HashMap<usize,Vec<((Transition,&[usize],&[usize]),usize)>> = HashMap::new();
    //     while let Some(z) = stack.pop() {
    //         for (f,a) in self.paths[z].0.iter() {
    //             for (i,c) in a.iter().copied().enumerate() {
    //                 if c==0 {continue;}
    //                 invocc.entry(c).or_default().push(((*f,&a[..i],&a[i+1..]),z));
    //                 match ownership.entry(c) {
    //                     Occupied(_)=>{},
    //                     Vacant(v)=>{
    //                         v.insert(1);
    //                         stack.push(c);
    //                         nonaccstates.push(c);
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //     let mut hotpools : HashSet<usize> = HashSet::new();
    //     hotpools.insert(0);
    //     let mut pools : Vec<(Vec<usize>,Vec<usize>)> = if nonaccstates.len()==0 {
    //         ownership.insert(0,1);
    //         vec![(accstates.clone(),Vec::new()),(vec![0],Vec::new())]
    //     } else {
    //         ownership.insert(0,2);
    //         hotpools.insert(1);
    //         vec![(accstates.clone(),Vec::new()),(nonaccstates,accstates.clone()),(vec![0],Vec::new())]
    //     };

    // }





    fn apply_simplification(&mut self,accstates:Vec<usize>,pools:Vec<(Vec<usize>,Vec<usize>)>,ownership:HashMap<usize,usize>)->Option<usize> {
        let mut hs = HashSet::new();
        let mut oup = Vec::new();
        for b in accstates {
            if hs.insert(b) {
                let own = ownership[&b];
                oup.push(own);
                hs.extend(pools[own].0.iter().copied());
                hs.extend(pools[own].1.iter().copied());
            }
        }
        if pools.iter().all(|(a,b)|a.len()==1&&b.len()==0) {
            if oup.len()==1 {return Some(pools[oup[0]].0[0])}
            let mut deps:Vec<(Transition,Vec<usize>)> = Vec::new();
            let chain : Vec<_> = oup.iter().map(|lv|pools[*lv].0.iter().map(|z|self.paths[*z].2.iter().copied()).flatten()).flatten().collect();
            for s in oup {deps.extend(self.paths[pools[s].0[0]].0.iter().cloned())}
            return Some(self.get_ntfa(deps,chain));
        }

        fn getmergedvl(
            sel:&NTFABuilder,
            item:usize,
            pools:&Vec<(Vec<usize>,Vec<usize>)>,
            ownership:&HashMap<usize,usize>
        )->IntoIter<(Transition,Vec<usize>)> {
            let mut deps:Vec<(Transition,Vec<usize>)> = Vec::new();
            for s in pools[item].0.iter().copied() {deps.extend(sel.paths[s].0.iter().cloned())}
            for s in pools[item].1.iter().copied() {deps.extend(sel.paths[s].0.iter().cloned())}
            deps.sort_unstable();
            deps.dedup();
            // println!("deps len: {:?} {:?} {:?}",deps.len(),pools[item].0.len(),pools[item].1.len());
            let mut a=0;
            // let OLDDEPS = deps.clone();
            while a<deps.len() {
                let f = deps[a].0;
                let l = deps[a].1.len();
                let mut b=1;
                while a+b<deps.len() && deps[a+b].0==f {
                    b+=1;
                }
                // if f==9 {println!("deps before after: {:?} {:?} {:?}",deps,a,b)}
                for amt in 0..l {
                    let mut x=0;
                    let mut partition=b;
                    while x<partition {
                        let mut y = x;
                        let mut fcollect:Vec<usize> = Vec::new();
                        // let mut DEBUG_HS2 = HashSet::new();
                        while y<partition {
                            if (0..l).all(|a2|a2==amt || deps[a+x].1[a2]==deps[a+y].1[a2]) {
                                let ncent = deps[a+y].1[amt];
                                // println!("{:?} (owner:{:?})",ncent,ownership[&ncent]);
                                // DEBUG_HS2.insert(ncent);
                                fcollect.push(ncent);
                                // if hs.insert(ncent) {
                                //     let own = ownership[&ncent];
                                //     collect.push(own);
                                //     // println!("extending {:?} {:?}",own,pools[own]);
                                //     hs.extend(pools[own].0.iter().copied());
                                //     // if pools[own].1.len()>0 {
                                //     //     collect.retain(|x|!pools[own].1.contains(x));//collect contains pool indices!
                                //     // }
                                //     hs.extend(pools[own].1.iter().copied());
                                // }
                                if y!=x {
                                    deps.remove(a+y);
                                    // if f==9 {println!("5 removal??! {:?}",RMRMRM);}
                                    b-=1;
                                    partition-=1;
                                } else {y+=1}
                            } else {y+=1;}
                        }
                        // let mut hs = HashSet::new();
                        let mut j=0;
                        while j<fcollect.len() {
                            let t = ownership[&fcollect[j]];
                            let oldl = fcollect.len();
                            fcollect.retain(|x|!pools[t].1.contains(x) && !pools[t].0[1..].contains(x));
                            if fcollect.len()<oldl {j=0;} else {j+=1;}
                        }
                        let mut collect = fcollect.into_iter().map(|w|ownership[&w]);
                        deps[a+x].1[amt]=match collect.next() {
                            Some(u)=>u,
                            None=>{
                                // println!("{:#?},{:?},{:?}",pools,hs,ownership);
                                panic!();
                            }
                        };
                        for col in collect {
                            let mut cr = deps[a+x].clone();
                            cr.1[amt] = col;
                            deps.insert(a+partition,cr);
                            b+=1;
                        }
                        x+=1;
                    }

                }
                // if f==9 {println!("deps snapshot after: {:?} {:?} {:?}",deps,a,b)}
                a+=b;
            }
            // println!("transform: {:?} => {:?}",OLDDEPS,deps);
            deps.sort_unstable();
            for (_,v) in deps.iter_mut() {
                v.reverse();
            }
            deps.into_iter()
        }
        struct ArtificialStack {
            outercollect: Vec<(Transition,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(Transition,Vec<usize>)>,
            innertrav: Vec<usize>,
            innertoken: Transition,
            mins : usize,
            place: usize,
        }
        let mut memo:HashMap<usize,usize> = HashMap::new();
        let mut result = Vec::new();
        for own in oup {
            let mut stack:Vec<ArtificialStack> = Vec::new();
            let place = match memo.entry(own) {
                Occupied(z)=>{
                    result.push(*z.get());
                    continue;
                }
                Vacant(z)=>{
                    let place = self.get_placeholder();
                    *z.insert(place)
                }
            };
            let mut outertrav = getmergedvl(self,own,&pools,&ownership);
            let (innertoken,intv) = outertrav.next().unwrap();
            stack.push(ArtificialStack{
                outercollect:Vec::new(),
                innercollect:Vec::new(),
                outertrav,
                innertoken,
                innertrav:intv,
                mins:pools[own].0.iter().chain(pools[own].1.iter()).map(|x|self.paths[*x].1.unwrap()).min().unwrap(),
                place,
            });
            //unevaluated gets cloned into a state besides unevaluated.
            while stack.len()>0 {
                let x = stack.last_mut().unwrap();
                loop {
                    if let Some(subl) = x.innertrav.pop() {
                        match if pools[subl].0.contains(&0) {Some(0)} else {memo.get(&subl).copied()} {
                            Some(y)=>{x.innercollect.push(y);continue;}
                            None=>{
                                let mut outertrav = getmergedvl(self,subl,&pools,&ownership);
                                if let Some((innertoken,intv)) = outertrav.next() {
                                    let place = self.get_placeholder();
                                    memo.insert(subl,place);
                                    x.innertrav.push(subl);
                                    stack.push(ArtificialStack{
                                        outercollect:Vec::new(),
                                        innercollect:Vec::new(),
                                        outertrav,
                                        innertoken,
                                        innertrav:intv,
                                        mins:pools[subl].0.iter().chain(pools[subl].1.iter()).map(|x|self.paths[*x].1.unwrap()).min().unwrap(),
                                        place,
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
                        let lastval = match stack.last() {
                            Some(x)=>*x.innertrav.last().unwrap(),
                            None=>own
                        };
                        let rpv = if ff.outercollect.len()==0 {panic!()} else {
                            let chain : Vec<_> = pools[lastval].0.iter().map(|z|self.paths[*z].2.iter().copied()).flatten().chain(
                                pools[lastval].1.iter().map(|z|self.paths[*z].2.iter().copied()).flatten()).collect();
                            let gov = self.insert_into_placeholder(ff.outercollect,ff.place,chain);
                            self.paths[gov].1 = Some(ff.mins);
                            gov
                        };
                        // if rpv != ff.place {panic!()}
                        if rpv != ff.place {
                            memo.insert(lastval,rpv);//harmlessly replace old value
                        }
                        if stack.len()==0 {
                            result.push(rpv);
                        }
                        break;
                    }
                }
            }
        }
        // panic!();
        if result.len()==0 {return None}
        if result.len()==1 {return Some(result[0])}
        let mut deps:Vec<(Transition,Vec<usize>)> = Vec::new();
        let chain : Vec<_> = result.iter().map(|z|self.paths[*z].2.iter().copied()).flatten().collect();
        for s in result {deps.extend(self.paths[s].0.iter().cloned())}
        return Some(self.get_ntfa(deps,chain));
    }
}

