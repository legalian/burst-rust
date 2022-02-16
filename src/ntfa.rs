

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
use ProcValue::{*};


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
    pub intersect_memo:HashMap<(usize,usize),Option<usize>>,//left side of key is less than right side
    pub rename_memo:HashMap<(usize,Vec<usize>),usize>,
    pub subset_memo:HashMap<(usize,usize),bool>,
    // minification_queue:Vec<usize>,
}

impl NTFABuilder {
    pub fn intersect(&mut self,mut a_start:usize,mut b_start:usize)->Option<usize> {
        // println!("ENTERING INTERSECT: {} {}",a_start,b_start);
        if a_start==b_start {return Some(a_start)}
        if a_start==0 {return Some(b_start)}
        if b_start==0 {return Some(a_start)}
        let key = (min(a_start,b_start),max(a_start,b_start));
        if let Some(early) = self.intersect_memo.get(&key) {return *early}
        let a_start_s = a_start;
        let b_start_s = b_start;
        #[derive(Debug)]
        struct OuterStack {
            a_start:usize,b_start:usize,
            ai:usize,bi:usize,
            deps_ab:Vec<(usize,Vec<usize>)>,
            innerstack:Vec<InnerStack>,
            placeab:usize,
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
            totalab:Vec<Vec<usize>>,
            yab : Option<Vec<Vec<usize>>>
        }
        let emptyr = vec![Vec::new()];
        let mut outerstack:Vec<OuterStack>=Vec::new();

        let mut ai=0;let mut bi=0;
        let mut deps_ab = Vec::new();

        let mut innerstack:Vec<InnerStack>=Vec::new();

        let mut placeab = self.get_placeholder();
        self.intersect_memo.insert(key,Some(placeab));
        
        'outerloop: loop {
            let al = &self.paths[a_start];
            let bl = &self.paths[b_start];
            // println!("from double top");
            // println!("begin outerloop: {:#?} astart:{} bstart:{} {:?}",outerstack,a_start,b_start,innerstack);
            // println!("-=-=-=-=-=-=-=-");
            'innerloop: while let Some(InnerStack{amt,alim,blim,x,y,abase,bbase,totalab,yab}) = innerstack.last_mut() {
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
                    let bp = bl[bbase+*y].1[amt];
                    let ap = al[abase+*x].1[amt];
                    let rw=if amt+1<fl {
                        if let Some(y)=yab {y} else {
                            // println!("whoa {} ({},{},{}) ({},{},{}) {:?} {:?}",amt,abase,x,alim,bbase,y,blim,al,bl);
                            let x=*x;let y=*y;
                            // if a_start==a_start_s && b_start==b_start_s {println!("pushing inner: x:{} y:{}, amt:{}",abase+x,bbase+y,amt+1);}
                            innerstack.push(InnerStack {
                                yab:None,
                                totalab:Vec::new(),
                                x:0,y:0,abase:abase+x,bbase:bbase+y,amt:amt+1,
                                alim:al[abase+x..].iter().take(alim).position(|(_,v)|v[amt] != al[abase+x].1[amt]).unwrap_or(alim-x),
                                blim:bl[bbase+y..].iter().take(blim).position(|(_,v)|v[amt] != bl[bbase+y].1[amt]).unwrap_or(blim-y)
                            });
                            // println!("from innerloop continue A!");
                            continue 'innerloop;
                        }
                    } else {&emptyr};

                    // if a_start==a_start_s && b_start==b_start_s {println!("doing an intersect: x:{} y:{}, amt:{}",abase+*x,bbase+*y,amt);}
                    let xab : Option<usize> = {
                        if ap==bp {Some(ap)}
                        else if ap==0 {Some(bp)}
                        else if bp==0 {Some(ap)}
                        else {
                            match self.intersect_memo.entry((min(ap,bp),max(ap,bp))) {
                                Occupied(z)=>*z.get(),
                                Vacant(_)=>{
                                    outerstack.push(OuterStack{
                                        a_start,b_start,
                                        ai,bi,
                                        deps_ab:take(&mut deps_ab),
                                        innerstack:take(&mut innerstack),
                                        placeab
                                    });
                                    ai=0;bi=0;
                                    a_start=ap;
                                    b_start=bp;
                                    placeab = self.get_placeholder();
                                    // println!("intersected: {:?} {:?} {:?}",(placeaa,placeab,placebb));
                                    let key = (min(ap,bp),max(ap,bp));
                                    self.intersect_memo.insert(key,Some(placeab));
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
                            totalab.push(we);
                        }
                    }
                    *yab=None;
                    let oy=&bl[bbase+*y].1[amt];*y+=1;
                    // println!("{:?} {:?} {:?}",bbase+*y,bbase+blim,bl);
                    while *y<blim && bl[bbase+*y].1[amt]==*oy {*y+=1;}
                    if *y>=blim {
                        let ox=&al[abase+*x].1[amt];*x+=1;
                        while *x<alim && al[abase+*x].1[amt]==*ox {*x+=1;}
                        if *x>=alim {break;}
                        *y=0;
                    }
                }

                let ff = innerstack.pop().unwrap();
                match innerstack.last_mut() {
                    Some(o)=>{
                        o.yab = Some(ff.totalab);
                    }
                    None=>{
                        let f=al[ai].0;
                        for j in ff.totalab {deps_ab.push((f,j));}
                        ai+=ff.alim;
                        bi+=ff.blim;
                        break;
                    }
                }
            }
            while ai<al.len() && bi<bl.len() {
                if al[ai].0<bl[bi].0 {ai+=1;}
                else if al[ai].0>bl[bi].0 {bi+=1;}
                else {
                    let f=al[ai].0;
                    if al[ai].1.len()==0 {
                        deps_ab.push((f,Vec::new()));
                        ai+=1;
                        bi+=1;
                    } else {
                        let alim=al[ai..].iter().position(|(f2,_)|*f2 != f).unwrap_or(al.len()-ai);
                        let blim=bl[bi..].iter().position(|(f2,_)|*f2 != f).unwrap_or(bl.len()-bi);
                        innerstack.push(InnerStack{
                            amt:0,alim,blim,
                            x:0,
                            y:0,
                            abase:ai,
                            bbase:bi,
                            totalab:Vec::new(),
                            yab:None,
                        });
                        continue 'outerloop;
                    }
                }
            }

            let rpvab = if deps_ab.len()==0 {None} else {Some(self.insert_into_placeholder(deps_ab,placeab))};
            
            if let Some(o) = outerstack.pop() {
                a_start=o.a_start;b_start=o.b_start;
                ai=o.ai;bi=o.bi;
                deps_ab=o.deps_ab;
                innerstack=o.innerstack;
                placeab=o.placeab;
                if rpvab != Some(placeab) {
                    let j = innerstack.last_mut().unwrap();

                    let r_key_a = self.paths[a_start][j.abase+j.x].1[j.amt];
                    let r_key_b = self.paths[b_start][j.bbase+j.y].1[j.amt];
                    self.intersect_memo.insert((min(r_key_a,r_key_b),max(r_key_a,r_key_b)),rpvab);//harmlessly replace old value
                }
            } else {
                if rpvab != Some(placeab) {
                    self.intersect_memo.insert((min(a_start_s,b_start_s),max(a_start_s,b_start_s)),rpvab);//harmlessly replace old value
                }
                return rpvab;
            }
        }
    }

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
    value:Vec<Option<usize>>,
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
                let u:Option<Vec<usize>> = ex[0][i].map(|z|m[i].recursion.get(&z).map(|x|x.iter().copied()).into_iter().flatten().collect());
                u
            });
            let mut cart : Vec<(_,Vec<Option<usize>>)> = vec![(mapping,Vec::new())];//I hate n-ary cartesian products
            for (bin,brow) in biz.enumerate() {
                if let Some(brow) = brow {
                    let mut buf = Vec::new();
                    if brow.len()==0 {return Vec::new()}
                    for (cmap,c) in cart {
                        'defeat: for b in brow.iter() {
                            let mut cmcl = cmap.clone();
                            if *b != 0 {
                                if let Some(bex) = ex[0][bin] {
                                    match &mut cmcl {
                                        None=>{
                                            let mut hm=HashMap::new();
                                            hm.insert(bex,*b);
                                            cmcl=Some(Rc::new(hm));
                                        },
                                        Some(x)=> match Rc::make_mut(x).entry(bex) {
                                            Vacant(hole) => {hole.insert(*b);}
                                            Occupied(spot) => {
                                                if *spot.get() != *b {continue 'defeat;}
                                            }
                                        }
                                    }
                                }
                            }
                            let mut cl = c.clone();
                            cl.push(Some(*b));
                            buf.push((cmcl,cl));
                        }
                    }
                    cart=buf;
                } else {
                    for (_,c) in cart.iter_mut() {c.push(None);}
                }
            }
            for (mapping,value) in cart {
                result.push(SolutionStatus {
                    dsl:dsl.clone(),size,value,mapping
                })
            }
        } else if a==9 {
            let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
                ex[0][i].and_then(|z|match &builder.values[z].0 {
                    LValue(_)=>ex[1][i],
                    RValue(_)=>ex[2][i],
                    _=>panic!()
                })
            }).collect();
            result.push(SolutionStatus {
                dsl,size,value,mapping
            })
        } else {
            let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
                ex.iter().map(|x|x[i]).try_fold(Vec::new(),|mut acc,x|{
                    if let Some(x)=x {
                        acc.push(x);Some(acc)
                    } else {None}
                }).and_then(|z|m[i].remap.get(&(a,z))).copied()
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
    // truthiness:HashMap<usize,bool>,
    remap:HashMap<(usize,Vec<usize>),usize>
}
impl ValueMapper {
    fn new()->Self {
        ValueMapper {
            recursion:HashMap::new(),
            // truthiness:HashMap::new(),
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

impl NTFABuilder {

    pub fn debug_is_accepting_run(&self,ntfa:usize,d:&Dsl,ex:&ExpressionBuilder)->bool {
        let (dslf,dsla) = match d {
            AccessStack(0)=>(1,Vec::new()),
            Lside(a)=>(5,vec![*a.clone()]),
            Rside(a)=>(6,vec![*a.clone()]),
            Pair(a,b)=>(2,vec![*a.clone(),*b.clone()]),
            BaseValue(x)=>match &ex.values[*x].0 {
                PairValue(a,b)=>(2,vec![BaseValue(*a),BaseValue(*b)]),
                LValue(a)=>(5,vec![BaseValue(*a)]),
                RValue(a)=>(6,vec![BaseValue(*a)]),
                UnitValue=>(0,Vec::new()),
                _=>panic!()
            },
            SwitchValue(c,a,b)=>(9,vec![*c.clone(),*a.clone(),*b.clone()]),
            LUndo(a)=>(7,vec![*a.clone()]),
            RUndo(a)=>(8,vec![*a.clone()]),
            LeftValue(a)=>(3,vec![*a.clone()]),
            RightValue(a)=>(4,vec![*a.clone()]),
            _=>panic!()
        };
        for (f,a) in self.paths[ntfa].iter() {
            if *f==dslf {
                if dsla.iter().zip(a.iter()).all(|(da,fa)|
                    self.debug_is_accepting_run(*fa,da,ex)
                ) {return true;}
            }
        } false
    }

}

#[derive(Default)]
pub struct PartialNTFA {
    pub rules:HashMap<usize,Vec<(usize,Vec<usize>)>>,
    occurances:HashMap<usize,HashSet<usize>>,
    maxins:usize,
    vm:ValueMapper
}
impl PartialNTFA {

    // pub fn debug_is_accepting_run(&self,d:&Dsl,ex:&ExpressionBuilder,accstates:&HashSet<usize>)->bool {
    //     if accstates.len()==0 {return false;}
    //     let (dslf,dsla) = match d {
    //         AccessStack(0)=>(1,Vec::new()),
    //         Lside(a)=>(5,vec![*a.clone()]),
    //         Rside(a)=>(6,vec![*a.clone()]),
    //         Pair(a,b)=>(2,vec![*a.clone(),*b.clone()]),
    //         BaseValue(x)=>match &ex.values[*x].0 {
    //             PairValue(a,b)=>(2,vec![BaseValue(*a),BaseValue(*b)]),
    //             LValue(a)=>(5,vec![BaseValue(*a)]),
    //             RValue(a)=>(6,vec![BaseValue(*a)]),
    //             UnitValue=>(0,Vec::new()),
    //             _=>panic!()
    //         },
    //         SwitchValue(c,a,b)=>(9,vec![*c.clone(),*a.clone(),*b.clone()]),
    //         LUndo(a)=>(7,vec![*a.clone()]),
    //         RUndo(a)=>(8,vec![*a.clone()]),
    //         LeftValue(a)=>(3,vec![*a.clone()]),
    //         RightValue(a)=>(4,vec![*a.clone()]),
    //         _=>panic!()
    //     };
    //     for i in accstates {
    //         for (f,a) in self.rules[i].iter() {
    //             if *f==dslf {
    //                 for (da,fa) in dsla.iter().zip(a.iter()) {
    //                     let mut nstates : HashSet<usize> = HashSet::new();
    //                     if !self.debug_is_accepting_run(&da,ex,&nstates) {return false}
    //                 }
    //                 // nstates.insert(a[ia]);
    //             }
    //         }
    //     } false
    // }

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
        let mut memo : HashMap<Vec<usize>,usize> = HashMap::new();
        let mut invmemo : HashMap<usize,Vec<usize>> = HashMap::new();
        let mut stack : Vec<((usize,Vec<usize>),HashSet<usize>)> = self.vm.recursion.iter().filter_map(|(a,bs)|
            if bs.len()<2 {None}
            else {Some(((10,vec![*a]),bs.clone()))}
        ).collect();
        while let Some(((f,a),bs)) = stack.pop() {
            let mut vv : Vec<usize> = bs.iter().map(|z|invmemo.get(z).cloned().unwrap_or(vec![*z])).flatten().collect();
            vv.sort_unstable();
            vv.dedup();
            let (early,nval) = match memo.entry(vv) {
                Occupied(z)=>(true,*z.get()),
                Vacant(z)=>{
                    let nval=self.maxins;self.maxins+=1;
                    invmemo.insert(nval,z.key().clone());
                    z.insert(nval);
                    (false,nval)
                }
            };
            // println!("{:?}",vv);
            self.rules.entry(nval).or_default().push((f,a.clone()));
            for a in a.iter() {
                self.occurances.entry(*a).or_default().insert(nval);
            }
            // println!("one {:?} {:?} {:?}",f,a,bs);
            for b in bs.iter() {
                self.rules.get_mut(b).unwrap().retain(|y|y.0 != f || y.1 != a);
            }
            if early {continue}
            let mut allocc = HashSet::new();
            let mut conflictcheck : HashMap<(usize,Vec<usize>),HashSet<usize>> = HashMap::new();
            for b in bs.iter() {
                allocc.extend(self.occurances.get(b).map(|x|x.iter().copied()).into_iter().flatten());
                if let Some(zs)=self.occurances.get(b) {
                    for z in zs {
                        let rows = self.rules.get_mut(z).unwrap();
                        let mut i=0;
                        while i<rows.len() {
                            for j in 0..rows[i].1.len() {
                                if rows[i].1[j] == *b {
                                    let mut nc = rows[i].clone();
                                    nc.1[j]=nval;
                                    conflictcheck.entry(nc.clone()).or_default().insert(*z);
                                    rows.push(nc);
                                }
                            }
                            i+=1;
                        }
                        rows.sort_unstable();
                        rows.dedup();
                    }
                }
            }
            self.occurances.insert(nval,allocc);
            // if conflictcheck.iter().any(|(_,b)|b.len()>=2) {
            //     panic!("two {:?}",conflictcheck.into_iter().filter(|(_,b)|b.len()>=2).collect::<Vec<_>>() );
            // }
            stack.extend(conflictcheck.into_iter().filter(|(_,b)|b.len()>=2));
        }
    }
    pub fn convert(self,builder:&mut NTFABuilder,ex:&ExpressionBuilder,accstates:&HashSet<usize>)->Option<(usize,ValueMapper)> {
        #[derive(PartialEq,PartialOrd,Eq,Ord,Clone,Hash,Debug)]
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
            // let OLDDEPS = deps.clone();
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
                            if if let Anything = deps[a+x].1[amt] {
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
                                    b+=1;false
                                } else {true}
                            } else {true} {
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
                                x+=1;
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
                                                .chain((amt+1..deps[i].1.len()).map(|_|Anything)).collect()));
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
            // println!("transform: {:?} => {:?}",OLDDEPS,deps);
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



