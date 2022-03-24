// use crate::nftabuilder::{*};
// use crate::spec::{*};
// use crate::nfta::{*};
// use crate::queue::{*};
// use std::collections::BinaryHeap;
// use std::collections::HashMap;
// use std::collections::HashSet;
// use std::cell::RefCell;
// use std::rc::Rc;
// use ProcValue::{*};
// use crate::debug::{*};
// use RefineLiteral::{*};


// pub fn new_synthesize(
//     mut exprbuilder:ExpressionBuilder,
//     spec:SingleSpecDisjunct,
//     input_type:usize,
//     output_type:usize
// ) {
//     let mut subex : SubexpressionFinder = SubexpressionFinder::new();
//     let mut nftabuilder = NFTABuilder::new(input_type,output_type);
//     let confirmer = spec.getconfirmer();
//     let mut heap = BinaryHeap::new();
//     heap.push(QueueElem{ item:spec, priority:0 });
//     while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
//         println!("popping!");
//         'specloop: for disjunct in spec.get_truesets().iter_mut() {
//             let mut order = disjunct.states.keys().copied().collect::<Vec<_>>();
//             order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);

//             // let mut debug_converted = Vec::new();
//             // let mut debug_intersected = Vec::new();
//             for (interp,a) in order.into_iter().enumerate() {
//                 println!("building nfta for: {:?}",DebugValue {
//                     t:a,
//                     expr:&exprbuilder
//                 });
//                 let newnfta = match nftabuilder.build_nfta(
//                     &mut exprbuilder,
//                     a,
//                     &confirmer,
//                     disjunct,
//                     &mut subex,
//                     100000,interp
//                 ) {
//                     Some(z)=>z,
//                     _=>{
//                         //mark into omega
//                         println!("No accepting states after nfta built");
//                         continue 'specloop
//                     }
//                 };
//                 // debug_converted.push(newnfta);
//                 disjunct.opnfta = match disjunct.opnfta {
//                     None=>Some(newnfta),
//                     Some(oldstate)=>{
//                         // println!("intersecting...");
//                         if let Some(intstate) = nftabuilder.intersect(newnfta,oldstate,None).and_then(|u|{nftabuilder.simplify(vec![u])})  {
//                             // debug_intersected.push(intstate);
//                             Some(intstate)
//                         } else {
//                             //mark into omega
//                             println!("No accepting states after intersection");
//                             continue 'specloop
//                         }
//                     }
//                 };
//             }
//             println!("generating accepting run!");
//             let nfta = disjunct.opnfta.unwrap();
//             let accrunlist = nftabuilder.get_accepting_runs(nfta,&mut exprbuilder);
//             if accrunlist.len()==0 {
//                 panic!("No accepting runs");
//                 continue 'specloop
//             }

//             let mut yessides = (0..accrunlist.len()).map(|_|spec.clone()).collect::<Vec<_>>();
//             let mut noside = spec;
//             for ((solution,solsize,witness),mut yesspec) in accrunlist.into_iter().zip(yessides.into_iter()) {
//                 println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);
//                 let dslsol = Rc::new(solution.clone());
//                 let tmemo = Rc::new(RefCell::new(HashMap::new()));
//                 if states.iter().all(|(key,val)|{
//                     let relval = exprbuilder.eval_recursive_function(dslsol.clone(),tmemo.clone(),*key);
//                     // println!("f({:?}) = {:?}",DebugValue {
//                     //     t:*key,
//                     //     expr:&exprbuilder
//                     // },DebugValue {
//                     //     t:relval,
//                     //     expr:&exprbuilder
//                     // });
//                     relval != 0 && val.accepts(relval) && confirmer.accepts(&mut exprbuilder,*key,relval)
//                 }) {
//                     println!("SOLUTION FOUND!");
//                     return;
//                 }
    
//                 println!("witness:");
//                 for (k,v) in witness.iter() {
//                     println!("\tf({:?}) = {:?}",DebugValue {
//                         t:*k,
//                         expr:&exprbuilder
//                     },DebugValue {
//                         t:*v,
//                         expr:&exprbuilder
//                     });
//                 }

//             }
//             return;
//             // let mut yes_side = spec.clone();
//             // let mut is_yes_ok = true;
//             // let disj : Vec<_> = witness.into_iter().map(|(k,v)|{
//             //     is_yes_ok = is_yes_ok && yes_side.refine(k,EqLit(v));
//             //     (k,NeqLit(v))
//             // }).collect();
//             // if is_yes_ok {
//             //     heap.push(QueueElem{ item:yes_side, priority:solsize });
//             // }
//             // if spec.refine_disjoint(disj) {
//             //     heap.push(QueueElem{ item:spec, priority:solsize });
//             // }
//             // break;
//         }
//     }
// }






