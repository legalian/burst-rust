// use crate::nftabuilder::{*};
// use crate::nfta::{*};
// use crate::acceptingrun::{*};
// use crate::dsl::{*};
// use std::collections::{*};
// use TermClassification::{*};
// use Transition::{*};
// use std::collections::hash_map::Entry::{*};
// use TypeMapType::{*};
// use ProcType::{*};
// use ProcValue::{*};
// use std::rc::Rc;
// use std::mem::{take};
// use std::cmp::Ordering;


// // predicate language:
// // AND (obvious)
// // func(self)
// // func(left(self))
// // func(right(self))
// // func(inl(self))
// // func(inr(self))
// // L+func(unl(self))
// // R+func(unr(self))
// // func((self,const))
// // func((const,self))

// // ^^^ you fucking got it


// // "yeah, well, the MEASURE(a(b(c(i(output))))) is a [0,6) and it should be a 6. new predicate: MEASURE(a(b(c(i(x)))))"
// // "or MEASURE(i^-1(c^-1(b^-1(a^-1(x)))))? for inverse? or  is the other one for inverse? make a punnett square for that and the inverse first-child-to-betray-set solution thingy"


// // MAKE PREDICATES THEMSELVES CONTAIN DSL

// // PUT IT IN MAIN.RS THAT DSLS SHOULD BE RC'ED


// // stubby:
// //     partial eval forward (Vec<Predlist>,Transition -> Predlist)
// //     alpha (Predlist,universe -> Predlist)
// //     widening (&mut universe,target:Predlist,children:Vec<Predlist> -> Vec<Predlist>)



// // f ( vec<predicate> ) -> any   [at first]
// // f ( vec<concrete predicate> ) -> actual

// // ^^^^ that should take care of initial building. Plus alpha, which in this case isn't much.

// // Then, you get an accepting run. Recursively widen it, as below. You can widen yourself and add yourself to
// //     the output list of predicates before considering children. Use the worklist impl, as stated in the paper.

// // just need to refine all your predicates. Widen the one on the very end, and only widen the ones that come before (recursively)
// // if they still logically imply the next node.
// // at first, this is pretty much just going to mean widening the root/accepting node i suppose.

// // widening func: it really depends on f. You have your minimal unwidened spec that can be simplified (and ought to be if the result is EQ, which it is)
// //     arbitrary func: can't widen your arguments. sorry.
// //     just throw a stub together. you'll see what to do after you have it stubbed. same goes for the other 2.

// #[derive(Clone,PartialEq,Eq,Hash,Debug)]
// enum SkeletonFilterNode {
//     Constfilt(usize,Vec<SkeletonFilter>),
//     Exactfilt(usize),
// }
// use SkeletonFilterNode::{*};
// type SkeletonFilter=Vec<SkeletonFilterNode>;
// // fn merge(a:SkeletonFilter,b:SkeletonFilter)->SkeletonFilter {
// //     let mut sk = a;
// //     'outer: for c in b {
// //         match c {
// //             Exactfilt(_)=>{
// //                 if !sk.contains(&c) {sk.push(c);}
// //             }
// //             Constfilt(cx,cl)=>{
// //                 for k in sk.iter_mut() {
// //                     if let Constfilt(x,l) = k {
// //                         if *x==cx {
// //                             *l = cl.into_iter().zip(take(l)).map(|(x,y)|merge(x,y)).collect();
// //                             continue 'outer;
// //                         }
// //                     }
// //                 }
// //                 sk.push(Constfilt(cx,cl));
// //             }
// //         }
// //     } sk
// // }


// #[derive(Clone,PartialEq,Eq,Hash,Debug)]
// pub enum Skeleton {
//     Constsk(usize,Vec<Skeleton>),
//     Exact(usize),
//     Hole
// }
// use Skeleton::{*};
// impl Skeleton {
//     fn filterrejecting(&self,b:usize,builder:&ExpressionBuilder)->Skeleton {
//         match (&builder.values[b].0,self) {
//             (_,Hole)=>Hole,
//             (Const(b,bl),Exact(e))=>match &builder.values[*e].0 {
//                 Const(a,al)=>{
//                     if a != b {return Constsk(*a,al.iter().map(|_|Hole).collect());}
//                     // let bl=bl.clone();
//                     let jj:Vec<_>=al.iter().zip(bl.iter()).map(|(a,b)|Exact(*a).filterrejecting(*b,builder)).collect();
//                     if jj.iter().any(|j|match j {Hole=>false,_=>true}) {
//                         Constsk(*a,jj)
//                     } else {Hole}
//                 }
//                 _=>panic!()
//             },
//             (Const(b,bl),Constsk(a,al))=>{
//                 if a != b {return Constsk(*a,al.iter().map(|_|Hole).collect());}
//                 // let bl=bl.clone();
//                 let jj:Vec<_>=al.iter().zip(bl.iter()).map(|(a,b)|a.filterrejecting(*b,builder)).collect();
//                 if jj.iter().any(|j|match j {Hole=>false,_=>true}) {
//                     Constsk(*a,jj)
//                 } else {Hole}
//             }
//             _=>panic!()
//         }
//     }
//     fn combine_into(&self,other:&mut SkeletonFilter,builder:&ExpressionBuilder) -> bool {
//         match self {
//             Hole=>{false},
//             Exact(n)=>if !other.contains(&Exactfilt(*n)) {
//                 other.push(Exactfilt(*n));
//                 true
//             } else {false},
//             Constsk(a,al)=>{
//                 for k in other.iter_mut() {
//                     if let Constfilt(b,bl) = k {
//                         if b==a {
//                             let mut ch = false;
//                             for (a,b) in al.iter().zip(bl.iter_mut()) {
//                                 ch = a.combine_into(b,builder) || ch;
//                             }
//                             return ch;
//                         }
//                     }
//                 }
//                 other.push(Constfilt(*a,al.iter().map(|_|Vec::new()).collect()));
//                 true
//             }
//         }
//     }
//     fn accepts(&self,b:usize,builder:&ExpressionBuilder)->bool {
//         match self {
//             Hole=>true,
//             Exact(e)=>*e==b,
//             Constsk(a,al)=>match &builder.values[b].0 {
//                 Const(b,bl)=>{
//                     if a != b {return false;}
//                     let bl=bl.clone();
//                     al.iter().zip(bl.iter()).all(|(a,b)|a.accepts(*b,builder))
//                 }
//                 _=>panic!()
//             }
//         }
//     }
//     fn filter(self,other:&SkeletonFilter,builder:&ExpressionBuilder)->Skeleton {
//         match self {
//             Hole=>Hole,
//             Exact(n)=>if other.contains(&Exactfilt(n)) {Exact(n)} else {
//                 match &builder.values[n].0 {
//                     Const(b,bl)=>{
//                         for k in other.iter() {
//                             if let Constfilt(a,al) = k {
//                                 if *b==*a {
//                                     let vv : Vec<_> = bl.into_iter().zip(al.iter()).map(|(b,a)|Exact(*b).filter(a,builder)).collect();
//                                     return if vv.iter().all(|v|match v {Exact(_)=>true,_=>false}) {Exact(n)}
//                                     else {Constsk(*a,vv)}
//                                 }
//                             }
//                         } Hole
//                     }
//                     _=>panic!()
//                 }
//             }
//             Constsk(a,al)=>{
//                 for k in other.iter() {
//                     if let Constfilt(b,bl) = k {
//                         if *b==a {
//                             return Constsk(a,al.into_iter().zip(bl.iter()).map(|(a,b)|a.filter(b,builder)).collect());
//                         }
//                     }
//                 } Hole
//             }
//         }
//     }
//     pub fn common(self,other:Skeleton,builder:&mut ExpressionBuilder)->Skeleton {
//         match (self,other) {
//             (Constsk(a,al),Constsk(b,bl))=>if a==b {
//                 Constsk(a,al.into_iter().zip(bl.into_iter()).map(|(a,b)|{
//                     a.common(b,builder)
//                 }).collect())
//             } else {Hole},
//             (Exact(a),Exact(b))=>if a==b {Exact(a)} else {Hole},
//             (Exact(a),Constsk(b,bl))=>{
//                 match &builder.values[a].0 {
//                     Const(a,al)=>{
//                         let al=al.clone();
//                         if *a != b {return Hole;}
//                         Constsk(*a,bl.into_iter().zip(al).map(|(b,a)|b.common(Exact(a),builder)).collect())
//                     }
//                     _=>panic!()
//                 }
//             }
//             (Constsk(a,al),Exact(b))=>{
//                 match &builder.values[b].0 {
//                     Const(b,bl)=>{
//                         let bl=bl.clone();
//                         if *b != a {return Hole;}
//                         Constsk(*b,al.into_iter().zip(bl).map(|(a,b)|a.common(Exact(b),builder)).collect())
//                     }
//                     _=>panic!()
//                 }
//             }
//             (_,Hole)|(Hole,_)=>Hole,
//         }
//     }
//     fn intersect(self,other:Skeleton,builder:&mut ExpressionBuilder)->Option<Skeleton> {
//         match (self,other) {
//             (Constsk(a,al),Constsk(b,bl))=>if a==b {
//                 let mut h=true;
//                 let ol = al.len();
//                 let z : Vec<_> = al.into_iter().zip(bl.into_iter()).filter_map(|(a,b)|{
//                     let g = a.intersect(b,builder);
//                     if let Some(Exact(_))=g {} else {h=false;} g
//                 }).collect();
//                 if z.len()!=ol {return None;}
//                 if h {return Some(Exact(builder.get_constructed(a,z.into_iter().map(|y|match y {Exact(x)=>x,_=>panic!()}).collect())))}
//                 Some(Constsk(a,z))
//             } else {None},
//             (Exact(a),Exact(b))=>if a==b {Some(Exact(a))} else {None},
//             (Exact(a),Constsk(b,bl))=>{
//                 match &builder.values[a].0 {
//                     Const(a,al)=>{
//                         let al=al.clone();
//                         if *a != b {return None;}
//                         if bl.into_iter().zip(al).any(|(b,a)|b.intersect(Exact(a),builder).is_none()) {return None;}
//                     }
//                     _=>panic!()
//                 } Some(Exact(a))
//             }
//             (Constsk(a,al),Exact(b))=>{
//                 match &builder.values[b].0 {
//                     Const(b,bl)=>{
//                         let bl=bl.clone();
//                         if *b != a {return None;}
//                         if al.into_iter().zip(bl).any(|(a,b)|a.intersect(Exact(b),builder).is_none()) {return None;}
//                     }
//                     _=>panic!()
//                 } Some(Exact(b))
//             }
//             (a,Hole)=>Some(a),
//             (Hole,b)=>Some(b)
//         }
//     }
// }

// impl PartialOrd for Skeleton {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         match (self,other) {
//             (Hole,Hole)=>Some(Ordering::Equal),
//             (Hole,_)=>Some(Ordering::Less),
//             (_,Hole)=>Some(Ordering::Greater),
//             (Constsk(ax,ay),Constsk(bx,by)) => Some((ax,ay).cmp(&(bx,by))),
//             (Constsk(_,_),_)=>Some(Ordering::Less),
//             (_,Constsk(_,_))=>Some(Ordering::Greater),
//             (Exact(a),Exact(b)) => Some(a.cmp(&b)),
//             // (Exact(_),_)=>Some(Ordering::Less),
//             // (_,Exact(_))=>Some(Ordering::Greater),
//         }
//     }
// }
// impl Ord for Skeleton {
//     fn cmp(&self,other:&Self) -> Ordering {
//         match (self,other) {
//             (Hole,Hole)=>Ordering::Equal,
//             (Hole,_)=>Ordering::Less,
//             (_,Hole)=>Ordering::Greater,
//             (Constsk(ax,ay),Constsk(bx,by)) => (ax,ay).cmp(&(bx,by)),
//             (Constsk(_,_),_)=>Ordering::Less,
//             (_,Constsk(_,_))=>Ordering::Greater,
//             (Exact(a),Exact(b)) => a.cmp(&b),
//             // (Exact(_),_)=>Ordering::Less,
//             // (_,Exact(_))=>Ordering::Greater,
//         }
//     }
// }



// #[derive(Clone,PartialEq,Eq,Hash,Debug)]
// enum Predicate {
//     Equal(Dsl,usize,Skeleton),
//     MeasureRange(Dsl,usize,Option<usize>),
// }
// use Predicate::{*};


// impl PartialOrd for Predicate {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         match (self,other) {
//             (Equal(ax,az,ay),Equal(bx,bz,by)) => Some((ax,az,ay).cmp(&(bx,bz,by))),
//             (Equal(_,_,_),_)=>Some(Ordering::Less),
//             (_,Equal(_,_,_))=>Some(Ordering::Greater),
//             (MeasureRange(ax,ay,az),MeasureRange(bx,by,bz)) => Some((ax,ay,az).cmp(&(bx,by,bz))),
//             // (MeasureRange(_,_,_),_)=>Some(Ordering::Less),
//             // (_,MeasureRange(_,_,_))=>Some(Ordering::Greater),
//         }
//     }
// }
// impl Ord for Predicate {
//     fn cmp(&self,other:&Self) -> Ordering {
//         match (self,other) {
//             (Equal(ax,az,ay),Equal(bx,bz,by)) => (ax,az,ay).cmp(&(bx,bz,by)),
//             (Equal(_,_,_),_)=>Ordering::Less,
//             (_,Equal(_,_,_))=>Ordering::Greater,
//             (MeasureRange(ax,ay,az),MeasureRange(bx,by,bz)) => (ax,ay,az).cmp(&(bx,by,bz)),
//             // (MeasureRange(_,_,_),_)=>Ordering::Less,
//             // (_,MeasureRange(_,_,_))=>Ordering::Greater,
//         }
//     }
// }



// struct Alphabet {
//     ranges:HashMap<(usize,Dsl),Vec<(usize,Option<usize>)>>,
//     equals:HashMap<(usize,Dsl),SkeletonFilter>,
// }
// impl Alphabet {
//     fn new()->Self {
//         Alphabet {
//             ranges:HashMap::new(),
//             equals:HashMap::new()
//         }
//     }
//     fn allow(&mut self,ty:usize,x:Predicate,builder:&mut ExpressionBuilder) -> bool {
//         match x {
//             Equal(x,_,sk)=>{
//                 sk.combine_into(self.equals.entry((ty,x)).or_default(),builder)
//             },
//             MeasureRange(x,min,max)=>{
//                 let gh = self.ranges.entry((ty,x)).or_default();
//                 if !gh.contains(&(min,max)) {gh.push((min,max)); true} else {false}
//             }
//         }
//     }
// }

// // Rooted() unique
// // MeasureRange(x,min,max) unique given x
// // Equal(x,whatever) unique given x


// type Predlist = Vec<Predicate>;
// impl AcceptableMap<usize,Predlist> for Vec<(Predlist,usize,TermClassification)> {
//     fn rem(&mut self,a:usize)->Predlist {take(&mut self[a].0)}
//     fn def()->usize {0}
// }
// impl Predicate {
//     fn discrim_difference_class_standard(&self,i:&[usize],builder:&mut ExpressionBuilder)->Option<Predicate> {
//         match self {
//             Equal(x,ty,sk) => match (builder.force_get_nat()==*ty,sk,builder.evaluate_solitary(x,i)) {
//                 (_,_,None)=>None,
//                 (true,Exact(sk),Some(discrim))=>{
//                     let num=builder.values[discrim].1-1;
//                     let targnum=builder.values[*sk].1-1;
//                     if num<targnum {Some(MeasureRange(x.clone(),0,Some(targnum)))}
//                     else if num>targnum {Some(MeasureRange(x.clone(),targnum+1,None))}
//                     else {None}
//                 },
//                 (_,_,Some(discrim))=>match sk.filterrejecting(discrim,builder) {
//                     Hole=>None,
//                     f=>Some(Equal(x.clone(),*ty,f))
//                 }
//             },
//             MeasureRange(x,min,max) => match builder.evaluate_solitary(x,i) {
//                 None=>None,
//                 Some(discrim)=>{
//                     let num=builder.values[discrim].1-1;
//                     if num<*min {return Some(MeasureRange(x.clone(),0,Some(*min)));}
//                     if let Some(z)=*max {
//                         if num>=z {return Some(MeasureRange(x.clone(),z+1,None));}
//                     } None
//                 }
//             }
//         }
//     }
// }
// impl SpecLike for Predlist {
//     fn get_narrow(&self)->Option<usize> {
//         if self.len()==1 {
//             if let Equal(Dsl::AccessStack(0),_,Exact(c)) = self[0] {
//                 return Some(c);
//             }
//         } None
//     }
//     fn moregeneral(&self,other:&Self,builder:&mut ExpressionBuilder)->bool {
//         if self.len()==0 {return true;}
//         if other.len()==0 {return false;}
//         match self.intersection(other,builder) {
//             None=>false,
//             Some(z)=>&z==other
//         }
//     }
//     fn intersection(&self,other:&Self,builder:&mut ExpressionBuilder)->Option<Self> {
//         if self.len()==0 {return Some(other.clone());}
//         if other.len()==0 {return Some(self.clone());}

//         let mut tself : Vec<Predicate> = if self.len()<other.len() {other.clone()} else {self.clone()};
//         let mut mergestack : Vec<Predicate> = if self.len()<other.len() {self.clone()} else {other.clone()};
//         'outer: while let Some(mut b) = mergestack.pop() {
//             for a in (0..tself.len()).rev() {
//                 match (&tself[a],b) {
//                     (MeasureRange(Dsl::AccessStack(0),_,Some(max)),Equal(Dsl::AccessStack(0),vt,v))=>{
//                         let mut max=*max;
//                         let mut w=&v;
//                         loop {
//                             match w {
//                                 Constsk(_,k)=>{
//                                     if max<2 {return None;}
//                                     max-=1;
//                                     w=&k[0];
//                                 }
//                                 _=>{break;}
//                             }
//                         }
//                         b=Equal(Dsl::AccessStack(0),vt,v);
//                     }
//                     (Equal(ax,a_s,ac),Equal(bx,bs,bc))=>if *ax==bx {
//                         if let Some(z) = ac.clone().intersect(bc.clone(),builder) {
//                             b=Equal(ax.clone(),bs,z);
//                             tself.remove(a);
//                         } else {return None;}
//                     } else {match (builder.nonvariablereasoning(ax,&bx,0,&bc),builder.nonvariablereasoning(&bx,ax,0,ac)) {
//                         ((_,_,false),(_,_,false))=>{b=Equal(bx,bs,bc)},
//                         ((_,_,false),(bn,_,true))=>{
//                             if !decompose_equal(bn,bs,bc,&mut mergestack,builder) {return None;}
//                             continue 'outer;
//                         },
//                         ((an,_,true),(_,_,false))=>{
//                             let a_s = *a_s;
//                             let ac = match tself.remove(a) {Equal(_,_,ac)=>ac,_=>panic!()};
//                             if !decompose_equal(an,a_s,ac,&mut mergestack,builder) {return None;}
//                             b=Equal(bx,bs,bc)
//                         },
//                         _=>panic!()
//                     }},
//                     (Equal(ax,_,ac),MeasureRange(bx,bmin,bmax))=>match builder.nonvariablereasoning(&bx,ax,0,ac) {
//                         (_,_,false)=>{b=MeasureRange(bx,bmin,bmax)},
//                         (bn,_,true)=>{
//                             if !decompose_measure(bn,bmin,bmax,&mut mergestack,builder) {return None;}
//                             continue 'outer;
//                         }
//                     },
//                     (MeasureRange(ax,amin,amax),Equal(bx,bs,bc))=>match builder.nonvariablereasoning(ax,&bx,0,&bc) {
//                         (_,_,false)=>{b=Equal(bx,bs,bc)},
//                         (an,_,true)=>{
//                             if !decompose_measure(an,*amin,*amax,&mut mergestack,builder) {return None;}
//                             tself.remove(a);
//                             b=Equal(bx,bs,bc);
//                         }
//                     },
//                     (MeasureRange(ax,amin,amax),MeasureRange(bx,bmin,bmax))=>if *ax==bx {
//                         let min=if *amin<bmin {*amin} else {bmin};
//                         let max=if let Some(amax)=*amax {
//                             if let Some(bmax)=bmax {
//                                 Some(if amax<bmax {amax} else {bmax})
//                             } else {Some(amax)}
//                         } else {bmax};
//                         if let Some(max)=max {
//                             if min>=max {return None;}
//                         }
//                         b=MeasureRange(ax.clone(),min,max);
//                         tself.remove(a);
//                     } else {b=MeasureRange(bx,bmin,bmax)}
//                 }
//             }
//             tself.push(b);
//         }
//         tself.sort_unstable();
//         Some(tself)
//     }
// }


// fn decompose_equal(a:Dsl,ty:usize,c:Skeleton,out:&mut Vec<Predicate>,builder:&mut ExpressionBuilder)->bool {
//     let mut stack = vec![(a,(c,ty))];
//     while let Some((u,(spec,ty)))=stack.pop() {
//         match u {
//             Dsl::BaseValue(y)=>{ if y==0 {continue;}; if spec.accepts(y,builder) {return false;} },
//             Dsl::Construct(a,v)=>match spec {
//                 Hole=>{}
//                 Constsk(b,bl)=>{
//                     if b != a {return false;}
//                     stack.extend(v.into_iter().zip(bl.into_iter().zip(builder.constructors[b].argtypes.iter().copied())));
//                 }
//                 Exact(e)=>match &builder.values[e].0 {
//                     Const(j,n)=>{
//                         if *j != a {return false;}
//                         stack.extend(v.into_iter().zip(n.iter().copied().map(|k|Exact(k)).zip(builder.constructors[*j].argtypes.iter().copied())));
//                     }
//                     _=>panic!()
//                 }
//             }
//             Dsl::Deconstruct(cstr,i,w)=>{
//                 let cst = &builder.constructors[cstr];
//                 let mut v = vec![Hole;cst.argtypes.len()];
//                 v[i]=spec;
//                 stack.push((*w,(Constsk(cstr,v),cst.restype)));
//             }
//             u=>{out.push(Equal(u,ty,spec));}
//         }
//     } true
// }
// fn decompose_measure(mut a:Dsl,mut min:usize,mut max:Option<usize>,out:&mut Vec<Predicate>,builder:&mut ExpressionBuilder)->bool {
//     loop {
//         match a {
//             Dsl::BaseValue(y)=>{
//                 if y==0 {continue;};
//                 let number = builder.values[y].1-1;
//                 if number < min {return false;}
//                 if let Some(max) = max {
//                     if number >= max {return false;}
//                 }
//                 return true;
//             },
//             Dsl::Deconstruct(_,_,v)=>{
//                 min+=1;
//                 if let Some(z) = &mut max {*z+=1;}
//                 a=*v;
//             }
//             Dsl::Construct(_,mut v)=>{
//                 if v.len()==0 {
//                     if min>0 {return false;}
//                     return true;
//                 } else {
//                     if min>0 {min-=1;}
//                     if let Some(z) = &mut max {
//                         *z-=1;
//                         if *z == min {return false;}
//                         if *z == min+1 {
//                             let bb = builder.force_get_nat();
//                             let os = builder.get_constructors_for(bb);
//                             let mut base = builder.get_constructed(os[0],Vec::new());
//                             for _ in 0..min {base = builder.get_constructed(os[1],vec![base]);}
//                             return decompose_equal(v.remove(0),bb,Exact(base),out,builder);
//                         }
//                     }
//                     a=v.remove(0);
//                 }
//             }
//             u=>{out.push(MeasureRange(u,min,max));return true;}
//         }
//     }
// }
// fn make_const_placeholder(cstr:usize,index:usize,builder:&mut ExpressionBuilder)->Dsl {
//     let mut v = vec![Dsl::BaseValue(0);builder.constructors[cstr].argtypes.len()];
//     v[index]=Dsl::AccessStack(0);
//     Dsl::Construct(cstr,v)
// }
// fn make_dest_placeholder(cstr:usize,index:usize)->Dsl {
//     Dsl::Deconstruct(cstr,index,Box::new(Dsl::AccessStack(0)))
// }

// fn make_full_const_placeholder(cstr:usize,other:&[usize],index:usize)->Dsl {
//     let mut v: Vec<_> = other.iter().map(|x|Dsl::BaseValue(*x)).collect();
//     v[index]=Dsl::AccessStack(0);
//     Dsl::Construct(cstr,v)
// }
// fn make_full_func_placeholder(w:usize,other:&[usize],index:usize,builder:&mut ExpressionBuilder)->Dsl {
//     let mut v: Vec<_> = other.iter().map(|x|Dsl::BaseValue(*x)).collect();
//     v[index]=Dsl::AccessStack(0);
//     Dsl::ApplyStack(Box::new(Dsl::BaseValue(builder.functions[w].concval)),v)
// }

// fn make_into_rcrow(a:Vec<Dsl>)->Rc<Vec<(Vec<Dsl>,usize)>>{
//     Rc::new(vec![(a,0)])
// }

// fn solo_predl_transform(s:&Predlist,r:Rc<Vec<(Vec<Dsl>,usize)>>,builder:&mut ExpressionBuilder)->Option<Predlist> {
//     let mut tself : Vec<_> = Vec::new();
//     for x in s.iter() {
//         match x {
//             Equal(x,ty,spec)=>{
//                 let u = builder.substitute(x,0,0,r.clone());
//                 if !decompose_equal(u,*ty,spec.clone(),&mut tself,builder) {return None;}
//             }
//             MeasureRange(x,min,max)=>{
//                 let u = builder.substitute(x,0,0,r.clone());
//                 if !decompose_measure(u,*min,*max,&mut tself,builder) {return None;}
//             }
//         }
//     }
//     tself.sort_unstable();
//     Some(tself)
// }

// //detect collisions between equal and range?
// //not allowed: [x,x), [x,x+1), Rooted(Hole), Equal(AccessStack(x),c), 
// //


// impl NFTABuilder<Predlist> {
//     pub fn build_afta(
//         &mut self,
//         builder:&mut ExpressionBuilder,
//         input:Predlist,
//         output:Predlist,
//         alphabet:&mut Alphabet,
//         interp:usize
//     )->Vec<usize> {
//         let mut processed_rel : HashMap<usize,Vec<usize>> = HashMap::new();//type:val,size
//         let mut queue : Vec<(Predlist,usize,TermClassification)> = Vec::new();
//         let mut visited : HashMap<(Predlist,usize,TermClassification),usize> = HashMap::new();
//         let mut accepting_states = Vec::new();
//         #[inline(always)]
//         fn expand(
//             alphabet : &Alphabet,
//             builder : &mut ExpressionBuilder,
//             amp : Predlist,
//             ty : usize
//         ) -> Predlist {
//             panic!("widen isn't powerful enough, for multiple reasons. One is that you need to comb through alphabet to see what you imply, and another is that you need the two-parter implication i.e. x=4,f(4,y)=10");
//             let mut mm : Vec<_> = amp.into_iter().filter_map(|y|match y {
//                 Equal(x,j,r)=>{
//                     let idex = (ty,x);
//                     if let Some(skf) = alphabet.equals.get(&idex) {
//                         match r.filter(skf,builder) {
//                             Hole=>None,
//                             z=>Some(Equal(idex.1,j,z))
//                         }
//                     } else {
//                         if let (Some(z),Exact(e))=(alphabet.ranges.get(&idex),r) {
//                             let number = builder.values[e].1-1;
//                             if let Some((min,max)) = z.iter().find(|(min,max)|{
//                                 if number<*min {return false;}
//                                 if let Some(max)=*max {
//                                     if number>=max {return false;}
//                                 } true
//                             }) {
//                                 Some(MeasureRange(idex.1,*min,*max))
//                             } else {None}
//                         } else {None}
//                     }
//                 }
//                 MeasureRange(x,lmin,lmax)=>{
//                     let idex = (ty,x);
//                     if let Some(z) = alphabet.ranges.get(&idex){
//                         if let Some((min,max)) = z.iter().find(|(min,max)|{
//                             if lmin<*min {return false;}
//                             match (lmax,*max) {
//                                 (Some(lmax),Some(max))=>lmax<=max,
//                                 (None,Some(_))=>false,
//                                 _=>true
//                             }
//                         }) {
//                             Some(MeasureRange(idex.1,*min,*max))
//                         } else {None}
//                     } else {None}
//                 }
//             }).collect();
//             mm.sort_unstable();
//             mm.dedup();
//             mm
//         }
//         #[inline(always)]
//         fn alpha(
//             alphabet : &Alphabet,
//             builder : &mut ExpressionBuilder,
//             queue : &mut Vec<(Predlist,usize,TermClassification)>,
//             visited : &mut HashMap<(Predlist,usize,TermClassification),usize>,
//             amp : Predlist,
//             ty : usize,
//             class : TermClassification,
//         )->usize {
//             let predlist = expand(alphabet,builder,amp,ty);
//             if predlist.len()==0 {return 0;}
//             match visited.entry((predlist,ty,class)) {
//                 Occupied(x)=>*x.get(),
//                 Vacant(x)=>{
//                     let qlen=queue.len();
//                     queue.push(x.key().clone());qlen
//                 }
//             }
//         }
//         #[inline(always)]
//         fn transfix(
//             alphabet : &Alphabet,
//             builder : &mut ExpressionBuilder,
//             queue : &mut Vec<(Predlist,usize,TermClassification)>,
//             visited : &mut HashMap<(Predlist,usize,TermClassification),usize>,
//             res : &mut PartialNFTA<usize>,
//             f : Transition,
//             args : Vec<usize>,
//             ty : usize,
//         ) {
//             match f {
//                 f@Destruct(cstr,i)=>{
//                     if let Some(z) = solo_predl_transform(&queue[args[0]].0,make_into_rcrow(vec![make_const_placeholder(cstr,i,builder)]),builder) {
//                         res.add_rule(f,args,alpha(alphabet,builder,queue,visited,z,ty,Elimination));
//                     }
//                 }
//                 f@Transition::Construct(cstr)=>{
//                     let mut zz = Vec::new();
//                     for (i,a) in args.iter().enumerate() {
//                         let z = match solo_predl_transform(&queue[*a].0,make_into_rcrow(vec![make_dest_placeholder(cstr,i)]),builder) {
//                             Some(z)=>z,None=>{return;}
//                         };
//                         if zz.len()==0 {zz=z}
//                         else {zz = match Predlist::intersection(&zz,&z,builder) {None=>{return;},Some(z)=>z}}
//                     }
//                     res.add_rule(f,args,alpha(alphabet,builder,queue,visited,zz,ty,Elimination));
//                 }
//                 f@ArbitraryFunc(w)=>{
//                     let sf : Vec<usize> = args.iter().filter_map(|e|
//                         if queue[*e].0.len()==1 {
//                             if let Equal(Dsl::AccessStack(0),_,Exact(x)) = &queue[*e].0[0] {
//                                 Some(*x)
//                             } else {None}
//                         } else {None}
//                     ).collect();
//                     let rres = if sf.len()==args.len() {
//                         vec![Equal(Dsl::AccessStack(0),ty,Exact(builder.exec_function(w,args.iter().copied().collect())))]
//                     } else {Vec::new()};
//                     res.add_rule(f,args,alpha(alphabet,builder,queue,visited,rres,ty,Introduction));
//                 }
//                 _=>panic!()
//             }
//         }
//         #[inline(always)]
//         fn can_rule_out_constructor(
//             builder:&ExpressionBuilder,
//             preds:&Predlist,
//             cstr:usize
//         )->bool {
//             // panic!("please refactor the constant matching into a property on skeleton.")
//             if preds.len()>0 {
//                 if let Equal(Dsl::AccessStack(0),_,Exact(x)) = preds[0] {
//                     match &builder.values[x].0 {
//                         Const(f,_)=>{return *f != cstr;}
//                         _=>panic!()
//                     }
//                 }
//                 if let Equal(Dsl::AccessStack(0),_,Constsk(a,_)) = preds[0] {
//                     if a != cstr {return true;}
//                 }
//             }
//             return false;
//         }
//         let mut res = PartialNFTA::new();
//         res.add_rule(Transition::Input,Vec::new(),
//             alpha(
//                 alphabet,builder,&mut queue,&mut visited,
//                 input,self.input_type,Elimination
//             )
//         );
//         for nul in builder.get_nullary_constructors() {
//             let rtype = builder.constructors[nul].restype;
//             transfix(
//                 alphabet,builder,&mut queue,&mut visited,&mut res,
//                 Transition::Construct(nul),Vec::new(),rtype
//             );
//         }
//         let mut gli = 0;
//         while gli<queue.len() {
//             let mut x = &queue[gli].0;
//             let xt = queue[gli].1;
//             let fresh = queue[gli].2;
//             if let Elimination = fresh {
//                 match &builder.types[xt] {
//                     EnumType(v)=>{
//                         let v=v.clone();
//                         for (w,cstr) in v.iter().zip(builder.get_constructors_for(xt)) {
//                             for (i,yt) in w.iter().enumerate() {
//                                 transfix(
//                                     alphabet,builder,&mut queue,&mut visited,&mut res,
//                                     Destruct(cstr,i),vec![gli],*yt,
//                                 );
//                                 x = &queue[gli].0;
//                             }
//                         }
//                     }
//                     _=>{}
//                 }
//             }
//             if let Elimination = fresh {
//                 for oli in 0..gli {
//                     let mut y = &queue[oli].0;
//                     let yt = queue[oli].1;
//                     let yfresh = queue[oli].2;
//                     match &builder.types[xt] {
//                         EnumType(v) if v.len()>1 =>{
//                             let vl=v.len();
//                             for (j,cstr) in builder.get_constructors_for(xt).into_iter().enumerate() {
//                                 if can_rule_out_constructor(builder,x,cstr) {continue;}
//                                 let mut nvm = vec![gli];
//                                 nvm.resize(1+vl,0);
//                                 nvm[j+1]=oli;
//                                 res.add_rule(Switch(vl),nvm,
//                                     if let Introduction=yfresh {oli} else {
//                                         let y=y.clone();
//                                         alpha(
//                                             alphabet,builder,&mut queue,&mut visited,
//                                             y,yt,Introduction
//                                         )
//                                     }
//                                 );
//                                 x = &queue[gli].0;
//                                 y = &queue[oli].0;
//                             }
//                         }
//                         _=>{}
//                     }
//                 }
//             }
//             for oli in 0..gli {
//                 let mut y = &queue[oli].0;
//                 let yt = queue[oli].1;
//                 let yfresh = queue[oli].2;
//                 if let Elimination = yfresh {
//                     match &builder.types[yt] {
//                         EnumType(v) if v.len()>1 =>{
//                             let vl=v.len();
//                             for (j,cstr) in builder.get_constructors_for(yt).into_iter().enumerate() {
//                                 if can_rule_out_constructor(builder,y,cstr) {continue;}
//                                 let mut nvm = vec![oli];
//                                 nvm.resize(1+vl,0);
//                                 nvm[j+1]=gli;
//                                 res.add_rule(Switch(vl),nvm,
//                                     if let Introduction=fresh {gli} else {
//                                         let x=x.clone();
//                                         alpha(
//                                             alphabet,builder,&mut queue,&mut visited,
//                                             x,xt,Introduction
//                                         )
//                                     }
//                                 );
//                                 x = &queue[gli].0;
//                                 y = &queue[oli].0;
//                             }
//                         }
//                         _=>{}
//                     }
//                 }
//             }
//             if xt==self.output_type {
//                 if output.moregeneral(x,builder) {
//                     accepting_states.push(gli);
//                 }
//             }
//             processed_rel.entry(xt).or_default().push(gli);
//             if let Some(z) = builder.stupid_typemap.get(&xt) {
//                 let z=z.clone();
//                 for (f_ind,s_ind) in z.iter() {
//                     let (argtypes,restype) = match f_ind {
//                         Function(x)=>{
//                             let FunctionEntry {argtypes,restype,..} = &builder.functions[*x];
//                             (argtypes,restype)
//                         }
//                         Constructor(x)=>{
//                             let ConstructorEntry {argtypes,restype,..} = &builder.constructors[*x];
//                             (argtypes,restype)
//                         }
//                     };
//                     let restype=*restype;
//                     let mut cartesian = vec![Vec::new()];
//                     for (i,argtype) in argtypes.into_iter().enumerate() {
//                         if i==*s_ind {
//                             for c in cartesian.iter_mut() {c.push(gli);}
//                             // println!("operated on cartesian {:?}",cartesian);
//                             continue;
//                         }
//                         let mut swap_buf = Vec::new();
//                         if let Some(v) = processed_rel.get(&argtype) {
//                             for u in v.iter() {
//                                 for cart in cartesian.iter() {
//                                     swap_buf.push({let mut cc=cart.clone();cc.push(*u);cc});
//                                 }
//                             }
//                         }
//                         cartesian=swap_buf;
//                         if cartesian.len()==0 {break;}
//                     }
//                     for cart in cartesian.into_iter() {
//                         transfix(
//                             alphabet,builder,&mut queue,&mut visited,&mut res,
//                             match f_ind {
//                                 Constructor(x)=>Transition::Construct(*x),
//                                 Function(x)=>ArbitraryFunc(*x)
//                             },cart,restype
//                         );
//                     }
//                 }
//             }
//             gli+=1;
//         }
//         res.convert(self,&accepting_states.iter().copied().collect(),interp,queue)
//     }
// }

















// #[derive(Clone,PartialEq,Eq,Hash,Debug)]
// enum AnnotatedAcceptingRunKind {
//     GetInput,
//     ApplyRecursive(Box<AnnotatedAcceptingRun>),
//     Deconstruct(usize,usize,Box<AnnotatedAcceptingRun>),
//     CustomFunc(usize,Vec<AnnotatedAcceptingRun>),
//     Construct(usize,Vec<AnnotatedAcceptingRun>),
//     SwitchValue(Box<AnnotatedAcceptingRun>,Vec<AnnotatedAcceptingRun>),
// }
// use AnnotatedAcceptingRunKind::{*};
// #[derive(Clone,PartialEq,Eq,Hash,Debug)]
// struct AnnotatedAcceptingRun {
//     kind:AnnotatedAcceptingRunKind,
//     node:usize,
//     values:Vec<Option<usize>>,
// }

// impl AcceptingRun {
//     fn get_annotated(self,inv:&[usize],builder:&mut ExpressionBuilder) -> AnnotatedAcceptingRun {
//         let uu : (AnnotatedAcceptingRunKind,Vec<Option<usize>>) = match self.kind {
//             AcceptingRunKind::GetInput=>(GetInput,inv.iter().map(|x|Some(*x)).collect()),
//             AcceptingRunKind::ApplyRecursive(x)=>(ApplyRecursive(Box::new(x.get_annotated(inv,builder))),inv.iter().map(|_|None).collect()),
//             AcceptingRunKind::Deconstruct(cstr,y,z)=>{
//                 let large=z.get_annotated(inv,builder);
//                 let j = large.values.iter().map(|x|match x {
//                     None=>None,
//                     Some(x)=>Some(match &builder.values[*x].0 {
//                         Const(a,al)=>{
//                             if *a != cstr {return None}
//                             al[y]
//                         }
//                         _=>panic!()
//                     })
//                 }).collect();
//                 (AnnotatedAcceptingRunKind::Deconstruct(cstr,y,Box::new(large)),j)
//             },
//             AcceptingRunKind::CustomFunc(w,v)=>{
//                 let v : Vec<_> = v.into_iter().map(|x|x.get_annotated(inv,builder)).collect();
//                 let vals = (0..inv.len()).map(|wj|{
//                     let u : Vec<_> = v.iter().filter_map(|k|k.values[wj]).collect();
//                     if u.len()<v.len() {None} else {Some(builder.exec_function(w,u))}
//                 }).collect();
//                 (CustomFunc(builder.functions[w].concval,v),vals)
//             },
//             AcceptingRunKind::Construct(w,v)=>{
//                 let v : Vec<_> = v.into_iter().map(|x|x.get_annotated(inv,builder)).collect();
//                 let vals = (0..inv.len()).map(|wj|{
//                     let u : Vec<_> = v.iter().filter_map(|k|k.values[wj]).collect();
//                     if u.len()<v.len() {None} else {Some(builder.get_constructed(w,u))}
//                 }).collect();
//                 (AnnotatedAcceptingRunKind::Construct(w,v),vals)
//             },
//             AcceptingRunKind::SwitchValue(x,y)=>{
//                 let dec = x.get_annotated(inv,builder);
//                 let v : Vec<_> = y.into_iter().map(|x|x.get_annotated(inv,builder)).collect();
//                 let vals = (0..inv.len()).map(|w|{
//                     match dec.values[w] {
//                         None=>None,
//                         Some(dec)=>match &builder.values[dec].0 {
//                             Const(a,_)=>v[builder.constructors[*a].index].values[w],
//                             _=>panic!()
//                         }
//                     }
//                 }).collect();
//                 (SwitchValue(Box::new(dec),v),vals)
//             },
//         };
//         AnnotatedAcceptingRun {
//             node:self.node,
//             kind:uu.0,
//             values:uu.1
//         }
//     }
// }


// // the negation of the target should be computable, into a disjunction of disjoint sections.
// //     you can obviously always fall back to the skeleton method.
// //     natural numbers will also always be inherently easy.
// //     more advanced methods include:
// //         inventing a measure
// //     worst method:
// //         absolute equality
// // also, consider that any predicate you made may already exist.

// // skeleton method????
// //     you can simply evaluate your witness on each dsl, and then skeleton/range method on whatever is left.
// //     you need to know the resultant type of each predicate DSL to know if you can range method.

// // impl 
// fn singlepredsplitconst(pred:&Predlist,i:&[usize],cstr:usize,builder:&mut ExpressionBuilder)->Vec<(usize,Predlist)> {
//     let mut v : Vec<_> = (0..i.len()).map(|s|(
//         builder.constructors[cstr].argtypes[s],
//         solo_predl_transform(pred,make_into_rcrow(vec![make_full_const_placeholder(cstr,i,s)]),builder).unwrap()
//     )).collect();
//     if i.len()>1 {
//         for (s,(j,ty)) in i.iter().zip(builder.constructors[cstr].argtypes.iter()).enumerate() {
//             v[s].1.push(Equal(Dsl::AccessStack(0),*ty,Exact(*j)))
//         }
//     }
//     for w in v.iter_mut() {
//         w.1.sort_unstable();
//         w.1.dedup();
//     } v
// }
// fn singlepredsplitfunc(pred:&Predlist,i:&[usize],w:usize,builder:&mut ExpressionBuilder)->Vec<(usize,Predlist)> {
//     let mut v : Vec<_> = (0..i.len()).map(|s|(
//         builder.functions[w].argtypes[s],
//         solo_predl_transform(pred,make_into_rcrow(vec![make_full_func_placeholder(w,i,s,builder)]),builder).unwrap()
//     )).collect();
//     if i.len()>1 {
//         for (s,(j,ty)) in i.iter().zip(builder.functions[w].argtypes.iter()).enumerate() {
//             v[s].1.push(Equal(Dsl::AccessStack(0),*ty,Exact(*j)))
//         }
//     }
//     for w in v.iter_mut() {
//         w.1.sort_unstable();
//         w.1.dedup();
//     } v
// }
// fn multipredsub(multipred:&Predlist,i:&[usize],ty:usize,builder:&mut ExpressionBuilder)->Vec<Predlist> {
//     let mut v : Vec<_> = (0..i.len()).map(|s|(
//         solo_predl_transform(multipred,make_into_rcrow(i.iter().enumerate().map(|(j,k)|{
//             if j==s {Dsl::AccessStack(0)}
//             else {Dsl::BaseValue(*k)}
//         }).collect()),builder).unwrap()
//     )).collect();
//     if i.len()>1 {
//         for (s,j) in i.iter().enumerate() {
//             v[s].push(Equal(Dsl::AccessStack(0),ty,Exact(*j)))
//         }
//     }
//     for w in v.iter_mut() {
//         w.sort_unstable();
//         w.dedup();
//     } v
// }

// impl AnnotatedAcceptingRun {
//     pub fn multitude_f_differentiate(
//         &self,
//         inputs:&[Predlist],
//         exprbuilder:&mut ExpressionBuilder,
//         nftabuilder:&NFTABuilder<Predlist>,
//         alphabet:&mut [Alphabet],
//         domain_narrowing_branches:&mut Vec<(usize,Predlist)>,
//     )->bool {
//         println!("it also counts as a CX if you get f(f(x)).");
//         //encounter f:
//             //input is not narrowed to nucleus WRT spec?
//                 //refine the nucleus(which will exist) to the widest interval that doesn't cross a spec boundary.
//                 //propogate that downwards.
//         let mut changed = false;
//         let mut stack = vec![(nftabuilder.output_type,self)];
//         while let Some((ty,node)) = stack.pop() {
//             match &node.kind {
//                 GetInput=>panic!(),
//                 ApplyRecursive(_)=>panic!(),
//                 SwitchValue(v,j)=>{
//                     let cstr = match exprbuilder.values[v.values[i].unwrap()].0 {
//                         Const(a,_)=>a,_=>panic!()
//                     };
//                     let cst = &exprbuilder.constructors[cstr];
//                     let index = cst.index;
//                     let restype = cst.restype;
//                     let argcount = cst.argtypes.len();
//                     stack.push((vec![Equal(Dsl::AccessStack(0),restype,Constsk(cstr,(0..argcount).map(|_|Hole).collect()))],i,restype,&v));
//                     stack.push((pred,i,ty,&j[index]));
//                 }
//                 Deconstruct(x,y,j)=>{
//                     let restype = exprbuilder.constructors[*x].restype;
//                     stack.push((restype,j))
//                 }
//                 AnnotatedAcceptingRunKind::Construct(x,j)=>{
//                     let omo : Vec<usize> = j.iter().map(|j|j.values[i].unwrap()).collect();
//                     for (node,(ty,pred)) in j.iter().zip(singlepredsplitconst(&pred,&omo,*x,exprbuilder)) {
//                         stack.push((pred,i,ty,node))
//                     }
//                 }
//                 CustomFunc(w,j)=>{
//                     let omo : Vec<usize> = j.iter().map(|j|j.values[i].unwrap()).collect();
//                     for (node,(ty,pred)) in j.iter().zip(singlepredsplitfunc(&pred,&omo,*w,exprbuilder)) {
//                         stack.push((pred,i,ty,node))
//                     }
//                 }
//             }

//         }
//         changed
//     }
//     pub fn populate_alphabet(
//         &self,
//         i:&[usize],
//         target:&Predlist,
//         inputs:&[Predlist],
//         exprbuilder:&mut ExpressionBuilder,
//         nftabuilder:&NFTABuilder<Predlist>,
//         alphabet:&mut [Alphabet],
//         domain_narrowing_branches:&mut Vec<(usize,Predlist)>
//     )->bool {
//         println!("anytime you construct Constsk, you need to have a justification for why it isn't Exact. For instance, in this function.");
//         //root node is Some, and doesn't satisfy the target predicate:
//             //differentiate and propogate the negative value!
//             //as you go, add each predicate into the alphabet.

//             //if you reach input(), and inputpred doesn't imply your current predicate:
//                 //branch into two:
//                     //one with (new predicate -> !output) in the decision tree(this run removed)
//                     //and one where you just narrow inputpred to new predicate both in the decision tree and this run.
//                 //in each branch, encounter all the fs starting at the old inputpred, process them as above. (make this just implicit?)
//         let trans_i : Vec<_> = i.iter().filter_map(|j|self.values[*j]).collect();
//         if trans_i.len()!=i.len() {return false;}//this spec has already deferred.
//         let root : Predlist = target.iter().filter_map(|pred|pred.discrim_difference_class_standard(&trans_i,exprbuilder)).collect();
//         if root.len()==0 {return false;}//this spec already succeeds.
//         let mut changed = false;
//         let mut stack = Vec::new();
//         for (i2,pl) in multipredsub(&root,&trans_i,nftabuilder.output_type,exprbuilder).into_iter().enumerate() {
//             stack.push((pl,i[i2],nftabuilder.output_type,self));
//         }
//         while let Some((pred,i,ty,node)) = stack.pop() {
//             let nodepred=&nftabuilder.paths[node.node].2.iter().find(|(j,_)|*j==i).unwrap().1;
//             for p in pred.iter() {
//                 changed = alphabet[i].allow(ty,p.clone(),exprbuilder) || changed;
//             }
//             match &node.kind {
//                 GetInput=>{
//                     let isect = inputs[i].intersection(&pred,exprbuilder).unwrap();
//                     if isect != inputs[i] {
//                         domain_narrowing_branches.push((i,isect));
//                     }
//                 },
//                 ApplyRecursive(_)=>panic!(),
//                 SwitchValue(v,j)=>{
//                     let cstr = match exprbuilder.values[v.values[i].unwrap()].0 {
//                         Const(a,_)=>a,_=>panic!()
//                     };
//                     let cst = &exprbuilder.constructors[cstr];
//                     let index = cst.index;
//                     let restype = cst.restype;
//                     let argcount = cst.argtypes.len();
//                     stack.push((vec![Equal(Dsl::AccessStack(0),restype,Constsk(cstr,(0..argcount).map(|_|Hole).collect()))],i,restype,&v));
//                     stack.push((pred,i,ty,&j[index]));
//                 }
//                 Deconstruct(x,y,j)=>{
//                     let restype = exprbuilder.constructors[*x].restype;
//                     let ch = solo_predl_transform(&pred,make_into_rcrow(vec![make_dest_placeholder(*x,*y)]),exprbuilder).unwrap();
//                     stack.push((ch,i,restype,j))
//                 }
//                 AnnotatedAcceptingRunKind::Construct(x,j)=>{
//                     let omo : Vec<usize> = j.iter().map(|j|j.values[i].unwrap()).collect();
//                     for (node,(ty,pred)) in j.iter().zip(singlepredsplitconst(&pred,&omo,*x,exprbuilder)) {
//                         stack.push((pred,i,ty,node))
//                     }
//                 }
//                 CustomFunc(w,j)=>{
//                     let omo : Vec<usize> = j.iter().map(|j|j.values[i].unwrap()).collect();
//                     for (node,(ty,pred)) in j.iter().zip(singlepredsplitfunc(&pred,&omo,*w,exprbuilder)) {
//                         stack.push((pred,i,ty,node))
//                     }
//                 }
//             }
//         }
//         changed
//     }
//     pub fn extract_positive(
//         &self,
//         i:Vec<usize>,
//         target:&Predlist,
//         exprbuilder:&mut ExpressionBuilder,
//         nftabuilder:&NFTABuilder<Predlist>,
//         alphabet:&mut [Alphabet]
//     )->Predlist {
//         let mut acell : Vec<usize> = Vec::new();
//         fn posextract(d:&AnnotatedAcceptingRun,i:usize,a:&mut Alphabet,acell:&mut Vec<usize>,builder:&mut ExpressionBuilder)->Dsl {
//             if let Some(z) = d.values[i] {
//                 return Dsl::BaseValue(z);
//             }
//             match &d.kind {
//                 GetInput=>panic!(),
//                 ApplyRecursive(d)=>{
//                     let nc = Dsl::AccessStack(acell.len());
//                     acell.push(d.values[i].unwrap()); nc
//                 },
//                 SwitchValue(v,j)=>{
//                     builder.get_switch(
//                         posextract(v,i,a,acell,builder),
//                         j.iter().map(|h|posextract(h,i,a,acell,builder)).collect()
//                     )
//                 }
//                 Deconstruct(x,y,v)=>{
//                     builder.get_deconstructor(
//                         *x,*y,
//                         posextract(v,i,a,acell,builder)
//                     )
//                 }
//                 AnnotatedAcceptingRunKind::Construct(x,j)=>{
//                     builder.get_construct_prog(
//                         *x,
//                         j.iter().map(|h|posextract(h,i,a,acell,builder)).collect()
//                     )
//                 }
//                 CustomFunc(w,j)=>{
//                     builder.get_applied(
//                         Dsl::BaseValue(builder.functions[*w].concval),
//                         j.iter().map(|h|posextract(h,i,a,acell,builder)).collect()
//                     )
//                 }
//             }
//         }

//         panic!()
//         //root node is None: ((if any met the previous criteria, skip this step.))
//             //propogate the positive value! but don't include those positive values in the alphabet
//             //encounter f:
//                 //input will be narrowed to nucleus WRT spec
//                     //yes->spec IO already decided on? pass.
//                         //otherwise, you're going to split the whole thing into two, one where the assignment is true, and one where it's false.
//     }
//     //separately, you need to include f transitions when FTA building!!! just use the spec to inform.
// }



// //you've got H1...
// //finding a solution can flow into f(x) if the value at x strictly differs from H1(x).









// // Issue when propogating positive spec!!!!!!
// // ---> allows relational expression to leak into the spec.


// // spawn them entangled?????????????


// // P(f(a),f(b))

// // [input predicate], output(predicate, DSL of n arguments.)









// // fn flat_synthesis(
// //     mut exprbuilder:ExpressionBuilder,
// //     spec:Vec<((Predlist,usize),Predlist)>,
// //     input_type:usize,
// //     output_type:usize
// // )->AcceptingRun {
// //     let mut nftabuilder = NFTABuilder::new(input_type,output_type);
// //     let mut alphabet = Alphabet::new();
// //     loop {
// //         let mut dfta_s = None;
// //         for (interp,(key,value)) in spec.iter().enumerate() {
// //             let dfta = nftabuilder.build_afta(
// //                 &mut exprbuilder,
// //                 key.clone(),
// //                 value.clone(),
// //                 &mut alphabet,
// //                 interp
// //             );
// //             dfta_s = Some(match dfta_s {
// //                 None=>dfta,
// //                 Some(x)=>nftabuilder.intersect(x,dfta,None)
// //             });
// //         }
// //         let dfta=dfta_s.unwrap();
// //         for (dsl,_,assign) in nftabuilder.get_accepting_runs(dfta,&mut exprbuilder) {

// //         }


// //     }
// // }



// // pub fn new_synthesize(
// //     mut exprbuilder:ExpressionBuilder,
// //     spec:Vec<(Predlist,Predlist)>,
// //     input_type:usize,
// //     output_type:usize
// // ) {
// //     let mut nftabuilder = NFTABuilder::new(input_type,output_type);
// //     let mut heap = BinaryHeap::new();
// //     heap.push(QueueElem{ item:spec, priority:0 });
// //     while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
// //         println!("popping!");
// //         let mut order = spec.states.keys().copied().collect::<Vec<_>>();
// //         order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);

// //         // let mut debug_converted = Vec::new();
// //         // let mut debug_intersected = Vec::new();
// //         for (interp,a) in order.into_iter().enumerate() {
// //             println!("building nfta for: {:?}",DebugValue {
// //                 t:a,
// //                 expr:&exprbuilder
// //             });
// //             let newnfta = match nftabuilder.build_nfta(
// //                 &mut exprbuilder,
// //                 a,
// //                 &confirmer,
// //                 spec,
// //                 &mut subex,
// //                 100000,interp
// //             ) {
// //                 Some(z)=>z,
// //                 _=>{
// //                     //mark into omega
// //                     println!("No accepting states after nfta built");
// //                     continue 'specloop
// //                 }
// //             };
// //             // debug_converted.push(newnfta);
// //             spec.opnfta = match spec.opnfta {
// //                 None=>Some(newnfta),
// //                 Some(oldstate)=>{
// //                     // println!("intersecting...");
// //                     if let Some(intstate) = nftabuilder.intersect(newnfta,oldstate,None).and_then(|u|{nftabuilder.simplify(vec![u])})  {
// //                         // debug_intersected.push(intstate);
// //                         Some(intstate)
// //                     } else {
// //                         //mark into omega
// //                         println!("No accepting states after intersection");
// //                         continue 'specloop
// //                     }
// //                 }
// //             };
// //         }
// //         println!("generating accepting run!");
// //         let nfta = spec.opnfta.unwrap();
// //         let accrunlist = nftabuilder.get_accepting_runs(nfta,&mut exprbuilder);
// //         if accrunlist.len()==0 {
// //             panic!("No accepting runs");
// //             continue 'specloop
// //         }

// //         let mut yessides = (0..accrunlist.len()).map(|_|spec.clone()).collect::<Vec<_>>();
// //         let mut noside = spec;
// //         for ((solution,solsize,witness),mut yesspec) in accrunlist.into_iter().zip(yessides.into_iter()) {
// //             println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);
// //             let dslsol = Rc::new(solution.clone());
// //             let tmemo = Rc::new(RefCell::new(HashMap::new()));
// //             if states.iter().all(|(key,val)|{
// //                 let relval = exprbuilder.eval_recursive_function(dslsol.clone(),tmemo.clone(),*key);
// //                 // println!("f({:?}) = {:?}",DebugValue {
// //                 //     t:*key,
// //                 //     expr:&exprbuilder
// //                 // },DebugValue {
// //                 //     t:relval,
// //                 //     expr:&exprbuilder
// //                 // });
// //                 relval != 0 && val.accepts(relval) && confirmer.accepts(&mut exprbuilder,*key,relval)
// //             }) {
// //                 println!("SOLUTION FOUND!");
// //                 return;
// //             }

// //             println!("witness:");
// //             for (k,v) in witness.iter() {
// //                 println!("\tf({:?}) = {:?}",DebugValue {
// //                     t:*k,
// //                     expr:&exprbuilder
// //                 },DebugValue {
// //                     t:*v,
// //                     expr:&exprbuilder
// //                 });
// //             }

// //         }
// //         return;
// //         // let mut yes_side = spec.clone();
// //         // let mut is_yes_ok = true;
// //         // let disj : Vec<_> = witness.into_iter().map(|(k,v)|{
// //         //     is_yes_ok = is_yes_ok && yes_side.refine(k,EqLit(v));
// //         //     (k,NeqLit(v))
// //         // }).collect();
// //         // if is_yes_ok {
// //         //     heap.push(QueueElem{ item:yes_side, priority:solsize });
// //         // }
// //         // if spec.refine_disjoint(disj) {
// //         //     heap.push(QueueElem{ item:spec, priority:solsize });
// //         // }
// //         // break;
    
// //     }
// // }






