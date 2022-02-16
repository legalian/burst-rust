

use std::collections::HashMap;
use std::collections::HashSet;
// use std::collections::VecDeque;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::mem::{take,replace};//,swap};
use std::iter::{*};
use std::iter::once;

use crate::dsl::{*};
use crate::nftabuilder::{*};
use crate::debug::{*};
// use crate::queue::{*};
use std::cmp::{min,max};
use std::vec::IntoIter;
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};
use ProcType::{*};


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
fn dedup_merge<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,None)=>{return c;}
            (Some(x),None)=>{c.push(x);c.extend(a);return c}
            (None,Some(y))=>{c.push(y);c.extend(b);return c}
            (Some(x),Some(y))=>{
                if x<y {c.push(x);xx=(a.next(),Some(y));} else
                if y<x {c.push(y);xx=(Some(x),b.next());} else
                {c.push(x);xx=(a.next(),b.next());}
            }
        }
    }
}
fn dedup_intersect<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,_)|(_,None)=>{return c;}
            (Some(x),Some(y))=>{
                if x<y {xx=(a.next(),Some(y));} else
                if y<x {xx=(Some(x),b.next());} else
                {c.push(x);xx=(a.next(),b.next());}
            }
        }
    }
}
fn dedup_setminus<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,_)=>{return c;}
            (Some(x),None)=>{c.push(x);c.extend(a);return c}
            (Some(x),Some(y))=>{
                if x<y {c.push(x);xx=(a.next(),Some(y));} else
                if y<x {xx=(Some(x),b.next());} else
                {xx=(a.next(),b.next());}
            }
        }
    }
}


pub struct NTFABuilder {
    pub input_type:usize,
    pub output_type:usize,
    pub paths:Vec<Vec<(usize,Vec<usize>)>>,//inner vec must be sorted
    pub revhash:HashMap<Vec<(usize,Vec<usize>)>,usize>,
    pub intersect_memo:HashMap<(usize,usize),(Option<usize>,Option<usize>,Option<usize>)>,//left side of key is less than right side
    pub rename_memo:HashMap<(usize,Vec<usize>),usize>,
    pub subset_memo:HashMap<(usize,usize),bool>,
    // minification_queue:Vec<usize>,
}

impl NTFABuilder {
    pub fn intersect(&mut self,mut a_start:usize,mut b_start:usize)->(Option<usize>,Option<usize>,Option<usize>) {
        println!("ENTERING INTERSECT: {} {}",a_start,b_start);
        if a_start==b_start {return (None,Some(0),None)}
        if a_start==0 {return (Some(0),Some(a_start),None)}
        if b_start==0 {return (None,Some(b_start),Some(0))}
        let key = (min(a_start,b_start),max(a_start,b_start));
        if let Some(early) = self.intersect_memo.get(&key) {
            return if b_start<a_start {
                let (x,y,z) = *early;(z,y,x)
            } else {*early}
        }
        let a_start_s = a_start;
        let b_start_s = b_start;
        #[derive(Debug)]
        struct OuterStack {
            a_start:usize,b_start:usize,
            ai:usize,bi:usize,
            totalaa:Vec<(usize,Vec<usize>)>,
            deps_ab:Vec<(usize,Vec<usize>)>,
            totalbb:Vec<(usize,Vec<usize>)>,
            innerstack:Vec<InnerStack>,
            placeaa:usize,
            placeab:usize,
            placebb:usize
        }
        #[derive(Debug)]
        struct InnerStack {
            amt:usize,
            alim:usize,
            blim:usize,
            x:usize,
            y:usize,
            abase:usize,
            bbase:usize,
            yi:usize,
            totalab:Vec<Vec<usize>>,
            bp : Vec<Option<usize>>,
            ap : usize,
            yab : Option<Vec<Vec<usize>>>
        }
        let emptyr = vec![Vec::new()];
        let mut outerstack:Vec<OuterStack>=Vec::new();

        let mut ai=0;let mut bi=0;
        let mut totalaa = Vec::new();
        let mut totalbb = Vec::new();
        let mut deps_ab = Vec::new();

        let mut innerstack:Vec<InnerStack>=Vec::new();

        let mut placeaa = self.get_placeholder();
        let mut placeab = self.get_placeholder();
        let mut placebb = self.get_placeholder();
        if b_start<a_start {
            self.intersect_memo.insert(key,(Some(placebb),Some(placeab),Some(placeaa)));
        } else {
            self.intersect_memo.insert(key,(Some(placeaa),Some(placeab),Some(placebb)));
        }
        
        'outerloop: loop {
            let al = &self.paths[a_start];
            let bl = &self.paths[b_start];
            // println!("from double top");
            // println!("begin outerloop: {:#?} astart:{} bstart:{} {:?}",outerstack,a_start,b_start,innerstack);
            // println!("-=-=-=-=-=-=-=-");
            'innerloop: while let Some(InnerStack{amt,alim,blim,x,y,abase,bbase,yi,totalab,bp,ap,yab}) = innerstack.last_mut() {
                // println!("innerloop: f:{},x:{},y:{}, amt:{}, yab:{:?} ",al[*abase+*x].0,*abase+*x,*bbase+*y,amt,yab);

                // if *amt != TODOREMOVE-1 {
                //     panic!()
                // }
                let abase=*abase;let bbase=*bbase;let amt=*amt;let alim=*alim;let blim=*blim;
                let fl=al[abase].1.len();
                if Some(fl)!=debug_expectedlen(al[abase].0) {panic!()}
                // println!("from top ");
                loop {
                    // println!("reached point: *x:{} amt:{},y:{},yi:{}, bplen:{}, bllen:{}, compolen:{}",*x,amt,bbase+*y,*yi,bp.len(),bl.len(),bl[bbase+*y].1.len());
                    if let Some(bps) = if bp.len()==*yi {Some(bl[bbase+*y].1[amt])} else {bp[*yi]} {
                        let rw=if amt+1<fl {
                            if let Some(y)=yab {y} else {
                                // println!("whoa {} ({},{},{}) ({},{},{}) {:?} {:?}",amt,abase,x,alim,bbase,y,blim,al,bl);
                                let x=*x;let y=*y;
                                // if a_start==a_start_s && b_start==b_start_s {println!("pushing inner: x:{} y:{}, amt:{}",abase+x,bbase+y,amt+1);}
                                innerstack.push(InnerStack {
                                    yab:None,
                                    bp:Vec::new(),
                                    ap:al[abase+x].1[amt+1].clone(),
                                    totalab:Vec::new(),
                                    x:0,y:0,yi:0,abase:abase+x,bbase:bbase+y,amt:amt+1,
                                    alim:al[abase+x..].iter().take(alim).position(|(_,v)|v[amt] != al[abase+x].1[amt]).unwrap_or(alim),
                                    blim:bl[bbase+y..].iter().take(blim).position(|(_,v)|v[amt] != bl[bbase+y].1[amt]).unwrap_or(blim)
                                });
                                // println!("from innerloop continue A!");
                                continue 'innerloop;
                            }
                        } else {&emptyr};

                        // for rz in rw.iter() {
                        //     if fl!=amt+rz.len()+1 {
                        //         let x=*x;let y=*y;let rzl=rz.len();
                        //         println!("{:#?}",innerstack);
                        //         println!("{:?}",deps_ab);
                        //         println!(" {:?} {} {}\n {:?} {} {}",al,abase+x,ai,bl,bbase+y,bi);
                        //         panic!("{}: {} {} {} ",al[abase].0,fl,amt,rzl)
                        //     }
                        // }
                        // println!("checking: {} {}",ap,bps);
                        let (xaa,xab,xbb) : (Option<usize>,Option<usize>,Option<usize>) = {
                            if *ap==bps {(None,Some(*ap),None)}
                            else if *ap==0  {(Some(0),Some(bps),None)}
                            else if bps==0 {(None,Some(*ap),Some(0))}
                            else {
                                let ap=*ap;
                                let key = (min(ap,bps),max(ap,bps));
                                match self.intersect_memo.entry(key) {
                                    Occupied(z)=>{
                                        if bps<ap {
                                            let (x,y,z) = *z.get();(z,y,x)
                                        } else {*z.get()}
                                    }
                                    Vacant(_)=>{

            // println!("{}^{} = ({:?},{:?},{:?}), ad={:?}, bd={:?}, center = {:?}",a_start,b_start,rpvaa,rpvab,rpvbb,self.paths[a_start],self.paths[b_start],deps_ab);
            
                                        outerstack.push(OuterStack{
                                            a_start,b_start,
                                            ai,bi,
                                            totalaa:take(&mut totalaa),totalbb:take(&mut totalbb),deps_ab:take(&mut deps_ab),
                                            innerstack:take(&mut innerstack),
                                            placeaa,placeab,placebb
                                        });
                                        ai=0;bi=0;
                                        a_start=ap;
                                        b_start=bps;
                                        placeaa = self.get_placeholder();
                                        placeab = self.get_placeholder();
                                        placebb = self.get_placeholder();
                                        // println!("intersected: {:?} {:?} {:?}",(placeaa,placeab,placebb));
                                        if bps<ap {
                                            self.intersect_memo.insert(key,(Some(placebb),Some(placeab),Some(placeaa)));
                                        } else {
                                            self.intersect_memo.insert(key,(Some(placeaa),Some(placeab),Some(placebb)));
                                        }
                                        // println!("pushing to outer stack new goal: {}^{} {:?} {:?}",a_start,b_start,self.paths[a_start],self.paths[b_start]);
                                        // println!("from outerloop continue A!");
                                        continue 'outerloop;
                                    }
                                }
                            }
                        };

                        if let Some(z) = xab {
                            for rz in rw.iter() {
                                let mut we = rz.clone();
                                we.insert(0,z);
                                // println!(" {} {} {} ",fl,amt,we.len());
                                if fl!=amt+we.len() {panic!(" {} {} {} ",fl,amt,we.len())}
                                totalab.push(we);
                            }
                        }
                        if bp.len()==*yi {bp.push(xbb);}
                        else {bp[*yi]=xbb;}
                        *ap=match xaa {Some(z)=>z,None=>{
                            // if a_start==a_start_s && b_start==b_start_s {println!("early abort: xaa is none. ap: {}, bps: {}, {},{} amt:{} ADEPS:{:?} BDEPS:{:?}",*ap,bps,abase+*x,bbase+*y,amt,self.paths[a_start],self.paths[b_start]);}
                            let ox=&al[abase+*x].1[amt];*x+=1;
                            while *x<alim && al[abase+*x].1[amt]==*ox {*x+=1;}
                            if *x>=alim {
                                // if a_start==a_start_s && b_start==b_start_s {println!("exiting (1) amt:{}",amt);}
                                break;
                            }
                            *ap=al[abase+*x].1[amt].clone();
                            *y=0;*yi=0;
                            // println!("from semibottom");
                            continue;
                        }};
                    }
                    // else {
                    //     if a_start==a_start_s && b_start==b_start_s {println!("skipped loop: bps is none");}
                    // }
                    // let OLDY = bbase+*y;
                    let oy=&bl[bbase+*y].1[amt];*y+=1;
                    while *y<blim && bl[bbase+*y].1[amt]==*oy {*y+=1;}
                    *yi+=1;
                    // if *x>
                    // println!("advancing yi;")
                    // if a_start==a_start_s && b_start==b_start_s {println!("advancing B {} to {}",OLDY,bbase+*y);}
                    if *y>=blim {
                        // let OLDX = abase+*x;

                        let ox=&al[abase+*x].1[amt];totalaa.push({let mut h=al[abase+*x].clone();h.1[amt]=ap.clone();h});*x+=1;
                        while *x<alim && al[abase+*x].1[amt]==*ox {totalaa.push({let mut h=al[abase+*x].clone();h.1[amt]=ap.clone();h});*x+=1;}
                        // if a_start==a_start_s && b_start==b_start_s {println!("advancing A {} to {}, resetting B",OLDX,abase+*x);}
                        if *x>=alim {
                            // if a_start==a_start_s && b_start==b_start_s {println!("exiting (2) amt:{}",amt);}
                            break;
                        }
                        *ap=al[abase+*x].1[amt].clone();
                        *y=0;*yi=0;
                    }
                    // println!("from bottom!");
                }
                let mut y = bbase;
                let mut yi = 0;
                while y<blim {
                    if yi==bp.len() {
                        totalbb.push(bl[bbase+y].clone());
                        y+=1;
                        continue;
                    }
                    let oy=&bl[bbase+y].1[amt];
                    if let Some(z)=&bp[yi] {totalbb.push({let mut h=bl[bbase+y].clone();h.1[amt]=z.clone();h});}
                    y+=1;
                    while y<blim && bl[bbase+y].1[amt]==*oy {
                        if let Some(z)=&bp[yi] {totalbb.push({let mut h=bl[bbase+y].clone();h.1[amt]=z.clone();h});}
                        y+=1;
                    }
                    yi+=1
                }
                // println!("reached end");
                // for i in 0..innerstack.len()-1 {
                //     if innerstack[i].amt+1!=innerstack[i+1].amt {
                //         panic!();
                //     }
                // }
                // for st in innerstack.iter() {
                //     for rz in st.totalab.iter() {
                //         if fl!=st.amt+rz.len() {panic!(" {} {} {} ",fl,amt,rz.len())}
                //     }
                // }
                let ff = innerstack.pop().unwrap();
                match innerstack.last_mut() {
                    Some(o)=>{
                        // if ff.totalab.len()>0 && fl!=ff.totalab[0].len()+o.amt+1 {
                        //     panic!("trouble");
                        // }
                        // if o.yab.is_some() {
                        //     panic!()
                        // }
                        o.yab = Some(ff.totalab);
                        // println!("assign to yab: from {:?}",innerstack);
                    }
                    None=>{
                        // if ai!=abase || bi!=bbase {
                        //     panic!();
                        // }
                        let f=al[ai].0;
                        for j in ff.totalab {

                            // if debug_expectedlen(f)!=Some(j.len()) {
                            //     panic!(
                            //         "addign: {},{:?}",f,j
                            //     );
                            // }

                            deps_ab.push((f,j));
                        }
                        ai+=ff.alim;
                        bi+=ff.blim;
                        break;
                    }
                }
            }
            // let mut int_anb=Vec::new();
            // let mut int_ab=Vec::new();
            while ai<al.len() && bi<bl.len() {
                if al[ai].0<bl[bi].0 {totalaa.push(al[ai].clone());ai+=1;}
                else if al[ai].0>bl[bi].0 {totalbb.push(bl[bi].clone());bi+=1;}
                else {
                    let f=al[ai].0;
                    if al[ai].1.len()==0 {
                        deps_ab.push((f,Vec::new()));
                        ai+=1;
                        bi+=1;
                    } else {
                        let alim=al[ai..].iter().position(|(f2,_)|*f2 != f).unwrap_or(al.len()-ai);
                        let blim=bl[bi..].iter().position(|(f2,_)|*f2 != f).unwrap_or(bl.len()-bi);
                        // println!("addressing: {} {} {} {:?} {:?}",f,alim,blim,al,bl);
                        innerstack.push(InnerStack{
                            amt:0,alim,blim,
                            x:0,
                            y:0,
                            abase:ai,
                            bbase:bi,
                            yi:0,
                            totalab:Vec::new(),
                            bp:Vec::new(),
                            ap:al[ai].1[0].clone(),
                            yab:None,
                        });
                        // println!("from outerloop continue B!");
                        continue 'outerloop;
                    }
                }
            }

    //                 let ff = stack.pop().unwrap();

            

            // panic!("do mergey simplify of everything");

            // let Some(bps) = if *x==0 {Some(&bl[bbase+*y].1[amt])} else {bp[*yi].as_ref()}



            let rpvaa = if totalaa.len()==0 {None} else {Some(self.insert_into_placeholder(totalaa,placeaa))};
            let rpvab = if deps_ab.len()==0 {None} else {Some(self.insert_into_placeholder(deps_ab,placeab))};
            let rpvbb = if totalbb.len()==0 {None} else {Some(self.insert_into_placeholder(totalbb,placebb))};

            // println!("{}^{} = ({:?},{:?},{:?}), ad={:?}, bd={:?}, center = {:?}",a_start,b_start,rpvaa,rpvab,rpvbb,self.paths[a_start],self.paths[b_start],deps_ab);
            
            if let Some(o) = outerstack.pop() {
                a_start=o.a_start;b_start=o.b_start;
                ai=o.ai;bi=o.bi;
                totalaa=o.totalaa;
                deps_ab=o.deps_ab;
                totalbb=o.totalbb;
                innerstack=o.innerstack;
                placeaa=o.placeaa;
                placeab=o.placeab;
                placebb=o.placebb;
                if rpvaa != Some(placeaa) || rpvab != Some(placeab) || rpvbb != Some(placebb) {
                    let j = innerstack.last_mut().unwrap();
                    // println!("");
                    // println!("WHATEVER 1 {:?}",self.paths[b_start]);
                    // println!("WHATEVER 2 {:?}",self.paths[b_start][j.bbase+j.y]);
                    // println!("WHATEVER 3 {:?}",self.paths[b_start][j.bbase+j.y].1[j.amt]);
                    // println!("WHATEVER 4 {:?}",self.paths[b_start][j.bbase+j.y].1[j.amt]);

                    let r_key_a = if j.yi==j.bp.len() {self.paths[b_start][j.bbase+j.y].1[j.amt]} else {j.bp[j.yi].unwrap()};
                    let r_key_b = j.ap;
                    if r_key_a<r_key_b {
                        self.intersect_memo.insert((r_key_a,r_key_b),(rpvaa,rpvab,rpvbb));//harmlessly replace old value
                    } else {
                        self.intersect_memo.insert((r_key_b,r_key_a),(rpvbb,rpvab,rpvaa));//harmlessly replace old value
                    }
                }
            } else {
                if rpvaa != Some(placeaa) || rpvab != Some(placeab) || rpvbb != Some(placebb) {
                    if a_start_s<b_start_s {
                        self.intersect_memo.insert((a_start_s,b_start_s),(rpvaa,rpvab,rpvbb));//harmlessly replace old value
                    } else {
                        self.intersect_memo.insert((b_start_s,a_start_s),(rpvbb,rpvab,rpvaa));//harmlessly replace old value
                    }
                }
                return (rpvaa,rpvab,rpvbb);
            }
        }
    }

    // fn indepth_simplify(&mut self,start:usize) {
    //     // if !self.closed_expr.insert(start) {return;}
    //     let mut deps = self.paths[start].clone();
    //     let mut a=0;
    //     while a<deps.len()-1 {
    //         let f = deps[a].0;
    //         let mut b=1;
    //         while deps[a+b].0==f {
    //             for c in 0..b {
    //                 let al = &deps[a+c].1;
    //                 let bl = &deps[a+b].1;
    //                 let mut i=0;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     "it wasn't deduped!";
    //                     // deps.remove(a+b);
    //                     // b-=1;break;
    //                 }
    //                 let l=i;
    //                 i+=1;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     let mut combo : Vec<_> = dedup_merge(self.paths[al[l]].clone(),self.paths[bl[l]].clone());
    //                     let mut rstack = Vec::new();
    //                     let mut d = b+1;
    //                     while a+d<deps.len() && deps[a+d].0==f {
    //                         if (0..deps[a+c].1.len()).all(|i|i==l || deps[a+d].1[i]==deps[a+c].1[i]) {
    //                             combo = dedup_merge(combo,self.paths[deps[a+d].1[l]].clone());
    //                             rstack.push(d);
    //                         }
    //                         d+=1;
    //                     }
    //                     // println!("stack: {} {:?}",b,rstack);
    //                     for r in rstack.into_iter().rev() {deps.remove(a+r);}
    //                     deps.remove(a+b);
    //                     let tmp = self.get_ntfa_unchecked(combo);
    //                     deps[a+c].1[l]=tmp;
    //                     b=0;break;
    //                 }
    //             }
    //             b+=1;
    //             if a+b>=deps.len() {break;}
    //         }
    //         a+=b;
    //     }
    //     self.revhash.insert(deps.clone(),start);
    //     self.paths[start] = deps;
    // }
    // fn small_simplification(deps: &mut Vec<(usize,Vec<usize>)>) {
    //     deps.sort_unstable();
    //     deps.dedup();
    // }
    // fn check_requires_further(deps: &[(usize,Vec<usize>)])->bool {
    //     let mut requires_further = false;
    //     let mut a=0;
    //     'outer: while a<deps.len()-1 {
    //         let f = deps[a].0;
    //         let mut b=1;
    //         while deps[a+b].0==f {
    //             for c in 0..b {
    //                 let al = &deps[a+c].1;
    //                 let bl = &deps[a+b].1;
    //                 let mut i=0;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {"wasn't deduped..."}
    //                 i+=1;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     // println!("rewuires: {}   {:?} {:?}",f,al,bl);
    //                     requires_further=true;
    //                     break 'outer;
    //                 }
    //             }
    //             b+=1;
    //             if a+b>=deps.len() {break;}
    //         }
    //         a+=b;
    //     } requires_further
    // }
    
    // fn get_ntfa(&mut self,mut deps:Vec<(usize,Vec<usize>)>)->usize {
    //     // NTFABuilder::small_simplification(&mut deps);
    //     self.get_ntfa_unchecked(deps)
    // }
    fn get_ntfa(&mut self,deps:Vec<(usize,Vec<usize>)>)->usize {
        match self.revhash.entry(deps) {
            Occupied(x)=>*x.get(),
            Vacant(x)=>{
                let i=self.paths.len();
                // if NTFABuilder::check_requires_further(x.key()) {
                //     self.minification_queue.push(i);
                // }
                self.paths.push(x.key().clone());
                x.insert(i); i
            }
        }
    }

    fn get_placeholder(&mut self)->usize {
        self.paths.push(vec![]);
        self.paths.len()-1
    }

    fn insert_into_placeholder(&mut self,mut deps:Vec<(usize,Vec<usize>)>,i:usize)->usize {
        deps.sort_unstable();
        deps.dedup();
        match self.revhash.entry(deps) {
            Occupied(x)=>*x.get(),//release i back to the cluster...
            Vacant(x)=>{
                // if NTFABuilder::check_requires_further(x.key()) {
                //     self.minification_queue.push(i);
                // }
                self.paths[i]=x.key().clone();
                x.insert(i); i
            }
        }
    }

    // pub fn forget_minification_queue(&mut self) {
    //     self.minification_queue = Vec::new();
    // }

    // pub fn deplete_minification_queue(&mut self) {
    //     while let Some(i) = self.minification_queue.pop() {
    //         self.indepth_simplify(i);
    //     }
    // }

    // pub fn getmergedvl(&self,ind:Vec<(usize,usize)>)->IntoIter<(usize,Vec<Vec<(usize,usize)>>)> {
    //     let mut buf_a:Vec<(usize,Vec<usize>)>;let mut buf_b:Vec<(usize,Vec<usize>)>;
    //     let (al,bl) : (&[(usize,Vec<usize>)],&[(usize,Vec<usize>)]) = if ind.len()>1 {
    //         buf_a = Vec::new();
    //         buf_b = Vec::new();
    //         for (sa,sb) in ind {
    //             buf_a.extend(self.paths[sa].clone());
    //             buf_b.extend(self.paths[sb].clone());
    //         }
    //         buf_a.sort_unstable();
    //         buf_b.sort_unstable();
    //         buf_a.dedup();
    //         buf_b.dedup();
    //         (&buf_a,&buf_b)
    //     } else {
    //         (&self.paths[ind[0].0],&self.paths[ind[0].1])
    //     };
    //     let mut a=0;
    //     let mut b=0;
    //     let mut ao;
    //     let mut bo;
    //     let mut deps = Vec::new();
    //     while a<al.len() && b<bl.len() {
    //         if al[a].0<bl[b].0 {a+=1;}
    //         else if al[a].0>bl[b].0 {b+=1;}
    //         else {
    //             let f=al[a].0;
    //             ao=0;
    //             bo=0;
    //             while a+ao<al.len() && al[a+ao].0==f {
    //                 bo=0;
    //                 while b+bo<bl.len() && bl[b+bo].0==f {
    //                     let mut res = Vec::new();
    //                     for i in 0..al[a+ao].1.len() {
    //                         res.push(vec![(min(al[a+ao].1[i],bl[b+bo].1[i]),max(al[a+ao].1[i],bl[b+bo].1[i]))]);
    //                     }
    //                     deps.push((f,res));
    //                     bo+=1;
    //                 }
    //                 ao+=1;
    //             }
    //             a+=ao;
    //             b+=bo;
    //         }
    //     }
    //     deps.sort_unstable();
    //     let mut a=0;
    //     while a+1<deps.len() {
    //         // println!("checkpoint 1: {} {}",deps.len(),a);
    //         let f = deps[a].0;
    //         let mut b=1;
    //         while deps[a+b].0==f {
    //             for c in 0..b {
    //                 let al = &deps[a+c].1;
    //                 let bl = &deps[a+b].1;
    //                 let mut i=0;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     deps.remove(a+b);
    //                     b-=1;break;
    //                 }
    //                 let l=i;
    //                 i+=1;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     let depr = take(&mut deps.remove(a+b).1[l]);
    //                     deps[a+c].1[l] = dedup_merge(take(&mut deps[a+c].1[l]),depr);
    //                     b=0;break;
    //                 }
    //             }
    //             b+=1;
    //             if a+b>=deps.len() {break;}
    //         }
    //         a+=b;
    //     } deps.into_iter()
    // }

    // pub fn intersect(&mut self,a_start:usize,b_start:usize) -> Option<usize> {
    //     if a_start==b_start {return Some(a_start);}
    //     struct ArtificialStack {
    //         outercollect: Vec<(usize,Vec<usize>)>,
    //         innercollect: Vec<usize>,
    //         outertrav: IntoIter<(usize,Vec<Vec<(usize,usize)>>)>,
    //         innertrav: Vec<Vec<(usize,usize)>>,
    //         innertoken: usize,
    //         place:usize
    //     }
    //     let mut stack:Vec<ArtificialStack> = Vec::new();
    //     let snok = vec![(min(a_start,b_start),max(a_start,b_start))];
    //     let place = self.get_placeholder();
    //     self.intersect_memo.insert(snok.clone(),Some(place));
    //     let mut outertrav = self.getmergedvl(snok);
    //     let (innertoken,intv) = match outertrav.next() {
    //         Some(x)=>x,None=>{return None;}
    //     };
    //     stack.push(ArtificialStack{
    //         outercollect:Vec::new(),
    //         innercollect:Vec::new(),
    //         outertrav,
    //         innertoken,
    //         innertrav:intv,
    //         place,
    //     });
    //     loop {
    //         let x = stack.last_mut().unwrap();
    //         loop {
    //             if let Some(subl) = x.innertrav.pop() {
    //                 match if subl.len()==1 && (subl[0].0==subl[0].1 || Some(subl[0].1)==self.uneval_hack) {Some(Some(subl[0].0))}
    //                     else if subl.len()==1 && Some(subl[0].0)==self.uneval_hack {Some(Some(subl[0].1))}
    //                     else {self.intersect_memo.get(&subl).copied()} {
    //                     Some(Some(y))=>{x.innercollect.push(y);continue;}
    //                     Some(None)=>{x.innercollect.clear();}
    //                     None=>{
    //                         let mut outertrav = self.getmergedvl(subl.clone());
    //                         if let Some((innertoken,intv)) = outertrav.next() {
    //                             let place = self.get_placeholder();
    //                             self.intersect_memo.insert(subl.clone(),Some(place));
    //                             x.innertrav.push(subl);
    //                             stack.push(ArtificialStack{
    //                                 outercollect:Vec::new(),
    //                                 innercollect:Vec::new(),
    //                                 outertrav,
    //                                 innertoken,
    //                                 innertrav:intv,
    //                                 place,
    //                             });
    //                             break;
    //                         } else {x.innercollect.clear();}
    //                     }
    //                 }
    //             } else {
    //                 let v = take(&mut x.innercollect);
    //                 x.outercollect.push((x.innertoken,v));
    //             }
    //             if let Some((innertoken,intv))=x.outertrav.next() {
    //                 x.innertoken=innertoken;
    //                 x.innertrav=intv;
    //             } else {
    //                 let ff = stack.pop().unwrap();
    //                 let rpv = if ff.outercollect.len()==0 {None} else {Some(self.insert_into_placeholder(ff.outercollect,ff.place))};
    //                 match stack.last() {
    //                     Some(x)=>{
    //                         if rpv != Some(ff.place) {
    //                             let fl = x.innertrav.last().unwrap();
    //                             self.intersect_memo.insert(fl.clone(),rpv);//harmlessly replace old value
    //                         }
    //                     }
    //                     None=>{
    //                         return rpv
    //                     }
    //                 }
    //                 break;
    //             }
    //         }
    //     }
    // }

    pub fn get_accepting_run(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder,
        map:&[ValueMapper]
    ) -> Vec<(Dsl,usize,HashMap<usize,usize>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus>>,usize,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus>>,usize,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x];
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        // println!("found nullary!");
                        for sol in SolutionStatus::transfix(*f,&vec![],map,builder) {
                            queue.push(SolutionStatusWrap(x,minsize+1,Some(sol)));
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
                    for sol in SolutionStatus::transfix(f,&v,map,builder) {
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
            (a.clone(),*b,c.as_ref().map(|x|(**x).clone()).unwrap_or_default())
        }).collect()
    }
}



#[derive(Clone,Debug)]
pub struct SolutionStatus {
    dsl:Dsl,
    size:usize,
    value:Vec<usize>,
    mapping:Option<Rc<HashMap<usize,usize>>>
}
#[derive(Debug)]
struct SolutionStatusWrap(usize,usize,Option<SolutionStatus>);
impl Eq for SolutionStatusWrap {}
impl Ord for SolutionStatusWrap {
    fn cmp(&self, other: &Self) -> Ordering {
        other.1.cmp(&self.1)
    }
}
impl PartialOrd for SolutionStatusWrap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.1.cmp(&self.1))
    }
}
impl PartialEq<SolutionStatusWrap> for SolutionStatusWrap {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}
impl SolutionStatus {
    fn compare_usefulness(&self,other:&SolutionStatus)->Ordering {
        let SolutionStatus{size:s,mapping:m,..} = other;
        match (if let Some(z)=m {//present subset of inserting
            if let Some(xx)=&self.mapping {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
            else {false}
        } else {true},
        if let Some(z)=&self.mapping {//inserting subset of present
            if let Some(xx)=m {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
            else {false}
        } else {true},self.size.cmp(s)) {
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
    fn transfix(
        a:usize,
        v:&Vec<Rc<SolutionStatus>>,
        m:&[ValueMapper],
        builder:&mut ExpressionBuilder
    )->Vec<SolutionStatus> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mapping = match v.iter().fold(Some(None),|a,x|match (a.clone(),x.mapping.clone()) {
            (None,_)=>None,
            (Some(None),None)=>Some(None),
            (Some(Some(x)),None)|(Some(None),Some(x))=>Some(Some(x)),
            (Some(Some(mut x)),Some(mut y))=>disjoint_union(
                take(Rc::make_mut(&mut x)),
                take(Rc::make_mut(&mut y))
            ).map(|x|Some(Rc::new(x)))
        }) {Some(x)=>x,None=>{return Vec::new();}};
        let v = v.iter().map(|x|&x.dsl).collect::<Vec<_>>();
        let mut result = Vec::new();
        let dsl = match a {
            0=>BaseValue(1),
            1=>AccessStack(0),
            2=>Pair(Box::new(v[0].clone()),Box::new(v[1].clone())),
            3=>builder.get_left_value(v[0].clone()),
            4=>builder.get_right_value(v[0].clone()),
            5=>builder.get_l_prog(v[0].clone()),
            6=>builder.get_r_prog(v[0].clone()),
            7=>builder.get_undo_left(v[0].clone()),
            8=>builder.get_undo_right(v[0].clone()),
            9=>SwitchValue(Box::new(v[0].clone()),Box::new(v[1].clone()),Box::new(v[2].clone())),
            10=>ApplyStack(Box::new(AccessStack(1)),v.into_iter().cloned().collect()),
            w=>ApplyStack(Box::new(BaseValue(builder.get_f_handle(w-11))),v.into_iter().cloned().collect()),
        };
        if a==10 {
            let biz = (0..m.len()).map(|i|{
                let u:Vec<_> = m[i].recursion.get(&ex[0][i]).map(|x|x.iter().copied()).into_iter().flatten().collect();
                u
            });
            let mut cart = vec![(mapping,Vec::new())];//I hate n-ary cartesian products
            for (bin,brow) in biz.enumerate() {
                let mut buf = Vec::new();
                if brow.len()==0 {return Vec::new()}
                for (cmap,c) in cart {
                    'defeat: for b in brow.iter() {
                        let mut cmcl = cmap.clone();
                        if ex[0][bin]!=0 && *b!=0 {
                            match &mut cmcl {
                                None=>{
                                    let mut hm=HashMap::new();
                                    hm.insert(ex[0][bin],*b);
                                    cmcl=Some(Rc::new(hm));
                                },
                                Some(x)=> match Rc::make_mut(x).entry(ex[0][bin]) {
                                    Vacant(hole) => {hole.insert(*b);}
                                    Occupied(spot) => {
                                        if *spot.get() != *b {continue 'defeat;}
                                    }
                                }
                            }
                        }
                        let mut cl = c.clone();
                        cl.push(*b);
                        buf.push((cmcl,cl));
                    }
                }
                cart=buf;
            }
            for (mapping,value) in cart {
                result.push(SolutionStatus {
                    dsl:dsl.clone(),size,value,mapping
                })
            }
        } else {
            let value:Vec<_> = (0..m.len()).filter_map(|i|{
                m[i].remap.get(&(a,ex.iter().map(|x|x[i]).collect())).copied()
            }).collect();
            result.push(SolutionStatus {
                dsl,size,value,mapping
            })
        }
        result
    }
}



pub type NTFA = usize;
#[derive(Default)]
pub struct ValueMapper {
    recursion:HashMap<usize,HashSet<usize>>,
    remap:HashMap<(usize,Vec<usize>),usize>
}
impl ValueMapper {
    fn new()->Self {
        ValueMapper {
            recursion:HashMap::new(),
            remap:HashMap::new()
        }
    }
}

#[derive(Clone,PartialOrd,PartialEq,Ord,Eq,Hash)]
pub enum InvType {
    BaseType(usize),
    FstType(Box<InvType>),
    SndType(Box<InvType>),
    LType(Box<InvType>),
    RType(Box<InvType>),
    SomeLR,
    Unknown
}
use InvType::{*};
impl InvType {
    fn canbe(&self,token:usize,builder:&ExpressionBuilder)->bool {
        match (self,&builder.types[token]) {
            (Unknown,_)=>true,
            (SomeLR,PairType(_,_))=>true,
            (SomeLR,_)=>false,
            (BaseType(i),_)=>*i==token,
            (FstType(i),PairType(a,_))=>i.canbe(*a,builder),
            (SndType(i),PairType(_,a))=>i.canbe(*a,builder),
            (LType(i),LRType(a,_))=>i.canbe(*a,builder),
            (RType(i),LRType(_,a))=>i.canbe(*a,builder),
            _=>false
        }
    }
    fn over(&self,token:usize,index:usize,builder:&NTFABuilder,ex:&ExpressionBuilder)->InvType {
        match (self,token,index) {
            (_,9,0)=>SomeLR,
            (x,9,1|2)=>x.clone(),
            (FstType(x),2,0)=>*x.clone(),
            (FstType(_),2,1)=>Unknown,
            (SndType(_),2,0)=>Unknown,
            (SndType(x),2,1)=>*x.clone(),
            (BaseType(x),2,0)=>BaseType(match &ex.types[*x] {PairType(a,_)=>*a,_=>{panic!()}}),
            (BaseType(x),2,1)=>BaseType(match &ex.types[*x] {PairType(_,a)=>*a,_=>{panic!()}}),
            (SomeLR,5,0)=>Unknown,
            (SomeLR,6,0)=>Unknown,
            (LType(x),5,0)=>*x.clone(),
            (RType(x),6,0)=>*x.clone(),
            (BaseType(x),5,0)=>BaseType(match &ex.types[*x] {LRType(a,_)=>*a,_=>{panic!()}}),
            (BaseType(x),6,0)=>BaseType(match &ex.types[*x] {LRType(_,a)=>*a,_=>{panic!()}}),
            (x,3,0)=>FstType(Box::new(x.clone())),
            (x,4,0)=>SndType(Box::new(x.clone())),
            (x,7,0)=>LType(Box::new(x.clone())),
            (x,8,0)=>RType(Box::new(x.clone())),
            (_,10,0)=>BaseType(builder.input_type),
            (Unknown,w,_) if w<11 =>Unknown,
            (_,w,a)=>BaseType(ex.functions[w-11].argtypes[a])
        }
    }
}

        // 0:unit        (0)
        // 1:input       (0)

        // 2:pair        (2)

        // 3:fst         (1)
        // 4:snd         (1)
        // 7:unl         (1)
        // 8:unr         (1)

        // 9:switch      (3)

        // 5:inl         (1)
        // 6:inr         (1)

        // 10:recursion  (1)
        // 11-onwards: free space!



#[derive(Default)]
pub struct PartialNTFA {
    pub rules:HashMap<usize,Vec<(usize,Vec<usize>)>>,
    occurances:HashMap<usize,HashSet<usize>>,
    maxins:usize,
    vm:ValueMapper
}
impl PartialNTFA {
    pub fn new()->Self {PartialNTFA{rules:HashMap::new(),occurances:HashMap::new(),vm:ValueMapper::new(),maxins:0}}
    pub fn add_rule(&mut self,f:usize,a:Vec<usize>,r:usize) {
        let mut m=r;
        for a in a.iter() {
            if *a>m {m=*a;}
            self.occurances.entry(*a).or_default().insert(r);
        }
        if m>=self.maxins {self.maxins=m+1;}
        if f==10 {
            self.vm.recursion.entry(a[0]).or_default().insert(r);
        } else {
            self.vm.remap.insert((f,a.clone()),r);
        }
        self.rules.entry(r).or_default().push((f,a));
    }
    pub fn determinize(&mut self) {
        let mut stack : Vec<((usize,Vec<usize>),HashSet<usize>)> = self.vm.recursion.iter().filter_map(|(a,bs)|
            if bs.len()<2 {None}
            else {Some(((10,vec![*a]),bs.clone()))}
        ).collect();
        while let Some(((f,a),bs)) = stack.pop() {
            let nval = self.maxins;self.maxins+=1;
            self.rules.entry(nval).or_default().push((f,a.clone()));
            for a in a.iter() {
                self.occurances.entry(*a).or_default().insert(nval);
            }
            let mut allocc = HashSet::new();
            let mut conflictcheck : HashMap<(usize,Vec<usize>),HashSet<usize>> = HashMap::new();
            for b in bs.iter() {
                allocc.extend(self.occurances.get(b).map(|x|x.iter().copied()).into_iter().flatten());
                self.rules.get_mut(b).unwrap().retain(|y|y.0 != f || y.1 != a);
                if let Some(zs)=self.occurances.get(b) {
                    for z in zs {
                        let rows = self.rules.get_mut(z).unwrap();
                        let mut i=0;
                        while i<rows.len() {
                            let mut j=0;
                            while j<rows[i].1.len() {
                                if rows[i].1[j] == *b {
                                    let mut nc = rows[i].clone();
                                    nc.1[j]=nval;
                                    conflictcheck.entry(nc.clone()).or_default().insert(*z);
                                    rows.push(nc);
                                }
                                j+=1;
                            }
                            i+=1;
                        }
                        rows.sort_unstable();
                        rows.dedup();
                    }
                }
            }
            self.occurances.insert(nval,allocc);
            stack.extend(conflictcheck.into_iter().filter(|(_,b)|b.len()>=2));
        }
    }
    pub fn convert(self,builder:&mut NTFABuilder,ex:&ExpressionBuilder,accstates:&HashSet<usize>)->Option<(usize,ValueMapper)> {
        #[derive(PartialEq,PartialOrd,Eq,Ord,Clone,Hash)]
        enum ConversionOption {
            Positive(Vec<usize>),
            Negative(Vec<usize>),
            Anything
        }
        use ConversionOption::{*};
        fn merge(a:ConversionOption,b:ConversionOption)->ConversionOption {
            match (a,b) {
                (Anything,_)|(_,Anything)=>Anything,
                (Positive(a),Positive(b))=>Positive(dedup_merge(a,b)),
                (Negative(a),Negative(b))=>Negative({
                    let j = dedup_intersect(a,b);
                    if j.len()==0 {return Anything} else {j}
                }),
                (Positive(a),Negative(b))|(Negative(b),Positive(a))=>Negative({
                    let j = dedup_setminus(b,a);
                    if j.len()==0 {return Anything} else {j}
                })
            }
        }
        fn negate(a:ConversionOption)->Option<ConversionOption> {
            match a {
                Positive(a)=>Some(Negative(a)),
                Negative(a)=>Some(Positive(a)),
                Anything=>None
            }
        }
        fn get_inversion_ledger(builder:&NTFABuilder,ex:&ExpressionBuilder,typeset:&InvType)->Vec<(usize,usize)> {
            let mut oros : Vec<(usize,usize)> = vec![(3,1),(4,1),(7,1),(8,1),(9,3)];
            if typeset.canbe(builder.output_type,ex) {oros.push((10,1));}
            oros.extend(
                (0..ex.get_f_count()).filter_map(|ff|{
                    let FunctionEntry {argtypes,restype,..} = &ex.functions[ff];
                    if typeset.canbe(*restype,ex) {
                        Some((11+ff,argtypes.len()))
                    } else {None}
                })
            );
            if typeset.canbe(builder.input_type,ex) {oros.push((1,0));}
            if typeset.canbe(0,ex) {oros.push((0,0));}
            match &typeset {
                Unknown=>{oros.push((2,2));}
                BaseType(x)=>match &ex.types[*x] {
                    PairType(_,_)=>{oros.push((2,2));}
                    _=>{}
                }
                FstType(_)=>{oros.push((2,2));}
                SndType(_)=>{oros.push((2,2));}
                _=>{}
            }
            match &typeset {
                SomeLR|Unknown=>{
                    oros.push((5,1));
                    oros.push((6,1));
                }
                BaseType(x)=>match &ex.types[*x] {
                    LRType(_,_)=>{
                        oros.push((5,1));
                        oros.push((6,1));
                    }
                    _=>{}
                }
                LType(_)=>{oros.push((5,1));}
                RType(_)=>{oros.push((6,1));}
                _=>{}
            }
            oros.sort_unstable();
            oros
        }
        fn getmergedvl<T:Iterator<Item=usize>>(
            sel:&PartialNTFA,
            builder:&NTFABuilder,
            ex:&ExpressionBuilder,
            ind:T,
            negative:bool,
            typeset:&InvType
        )->IntoIter<(usize,Vec<ConversionOption>)> {
            let mut deps:Vec<(usize,Vec<ConversionOption>)> = Vec::new();
            for s in ind {deps.extend(sel.rules.get(&s).into_iter().map(|ii|ii.iter().map(|(f,a)|
                (*f,a.iter().map(|x|if *x==0 {Anything} else {Positive(vec![*x])}).collect())
            )).flatten());}
            deps.sort_unstable();
            deps.dedup();
            let mut a=0;
            while a+1<deps.len() {
                let f = deps[a].0;
                let l = deps[a].1.len();
                let mut b=1;
                while deps[a+b].0==f {
                    b+=1;
                    if a+b>=deps.len() {break;}
                }
                for x in 0..b-1 {
                    let mut y=x+1;
                    while y<b {
                        if (0..l).all(|a2|deps[a+x].1[a2]==deps[a+y].1[a2] || deps[a+x].1[a2]==Anything || deps[a+y].1[a2]==Anything) {
                            let depr = take(&mut deps.remove(a+y).1);
                            for (rr,kk) in deps[a+x].1.iter_mut().zip(depr.into_iter()) {
                                if kk==Anything {*rr=Anything;}
                            }
                            b-=1;
                        } else {
                            y+=1;
                        }
                    }
                }
                if b != 1 {
                    for amt in 0..l {
                        let mut x=0;
                        while x<b {
                            if let Anything = deps[a+x].1[amt] {
                                let mut ooc = Vec::new();
                                for y in 0..b {
                                    if let Positive(k) = &deps[a+y].1[amt] {
                                        if (0..amt).all(|i|deps[a+y].1[i]==deps[a+x].1[i]) {
                                            ooc.push(k[0]);
                                        }
                                    }
                                }
                                if ooc.len()>0 {
                                    let mut rag = deps[a+x].clone();
                                    rag.1[amt]=Negative(ooc.clone());
                                    deps[a+x].1[amt]=Positive(ooc);
                                    deps.insert(a+x+1,rag);
                                    b+=1;
                                } else {x+=1;}
                            } else {x+=1;}
                        }
                    }
                    for amt in (0..l).rev() {
                        for x in 0..b {
                            let mut y = x+1;
                            while y<b {
                                if (0..l).all(|a2|a2==amt || deps[a+x].1[a2]==deps[a+y].1[a2]) {
                                    let depr = replace(&mut deps.remove(a+y).1[amt],Anything);
                                    deps[a+x].1[amt] = merge(replace(&mut deps[a+x].1[amt],Anything),depr);
                                    b-=1;
                                } else {
                                    y+=1;
                                }
                            }
                        }
                    }
                }
                a+=b;
            }
            if negative {
                let mut i=0;
                let mut oros : Vec<(usize,Vec<ConversionOption>)> = Vec::new();
                for (kf,kt) in get_inversion_ledger(builder,ex,typeset) {
                    while i<deps.len() && deps[i].0>kf {i+=1}
                    if i>=deps.len() {
                        oros.push((kf,(0..kt).map(|_|Anything).collect()));
                        continue;
                    }
                    if kt==0 {i+=1;continue;}
                    let mut j = i+1;
                    while j<deps.len() && deps[i].0==deps[j].0 {j+=1;}
                    let mut stack = vec![(i,j)];
                    'outer: while let Some((i,j))=stack.last().copied() {
                        let amt = stack.len()-1;
                        if amt==deps[i].1.len() {
                            loop {
                                let (i,j) = stack.pop().unwrap();
                                let amt = stack.len()-1;
                                if let Some(z) = deps[i..j].iter().map(|v|v.1[amt].clone()).reduce(merge).and_then(negate) {
                                    oros.push((deps[i].0,deps[i].1[..amt].iter().cloned()
                                                .chain(once(z))
                                                .chain(deps[i].1[amt+1..].iter().cloned()).collect()));
                                }
                                match stack.last_mut() {
                                    None=>{break 'outer;}
                                    Some((ip,jp))=>{
                                        if *jp==j {continue}
                                        *ip=j;continue 'outer;
                                    }
                                }
                            }
                        }
                        let mut k=i+1;
                        while k<j && deps[i].1[amt]==deps[k].1[amt] {k+=1;}
                        stack.push((i,k));
                    }
                    i=j;
                }
                deps = oros;
            }
            deps.sort_unstable();
            for (_,v) in deps.iter_mut() {
                v.reverse();
            }
            deps.into_iter()
        }
        if accstates.len()==0 {return None}
        struct ArtificialStack {
            outercollect: Vec<(usize,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(usize,Vec<ConversionOption>)>,
            innertrav: Vec<ConversionOption>,
            innertoken: usize,
            place: usize,
            types: InvType
        }
        let mut stack:Vec<ArtificialStack> = Vec::new();
        let mut memo:HashMap<ConversionOption,Option<usize>> = HashMap::new();
        memo.insert(Anything,Some(0));

        let mut snok = accstates.iter().copied().collect::<Vec<_>>();
        snok.sort_unstable();

        let place = builder.get_placeholder();
        memo.insert(Positive(snok.clone()),Some(place));
        let intype = BaseType(builder.output_type);
        let mut outertrav = getmergedvl(&self,builder,ex,accstates.iter().copied(),false,&intype);
        let (innertoken,intv) = outertrav.next().unwrap();
        stack.push(ArtificialStack{
            outercollect:Vec::new(),
            innercollect:Vec::new(),
            outertrav,
            innertoken,
            innertrav:intv,
            place,
            types: intype
        });
        loop {
            let x = stack.last_mut().unwrap();
            loop {
                if let Some(subl) = x.innertrav.pop() {
                    match memo.get(&subl).copied() {
                        Some(Some(y))=>{x.innercollect.push(y);continue;}
                        Some(None)=>{x.innercollect.clear();}
                        None=>{
                            let (inn,neg) = match &subl {Anything=>panic!(),Positive(inn)=>(inn,false),Negative(inn)=>(inn,true)};
                            let mut outertrav = getmergedvl(&self,builder,ex,inn.iter().copied(),neg,&x.types);
                            if let Some((innertoken,intv)) = outertrav.next() {
                                let place = builder.get_placeholder();
                                memo.insert(subl.clone(),Some(place));
                                x.innertrav.push(subl);
                                let nn = x.types.over(x.innertoken,x.innercollect.len(),builder,ex);
                                stack.push(ArtificialStack{
                                    outercollect:Vec::new(),
                                    innercollect:Vec::new(),
                                    outertrav,
                                    innertoken,
                                    innertrav:intv,
                                    place,
                                    types:nn
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
                    let rpv = if ff.outercollect.len()==0 {None} else {Some(builder.insert_into_placeholder(ff.outercollect,ff.place))};
                    match stack.last() {
                        Some(x)=>{
                            if rpv != Some(ff.place) {
                                let fl = x.innertrav.last().unwrap();
                                memo.insert(fl.clone(),rpv);//harmlessly replace old value
                            }
                        }
                        None=>{
                            // builder.deplete_minification_queue();
                            return rpv.map(|x|(x,self.vm))
                        }
                    }
                    break;
                }
            }
        }
    }
}



