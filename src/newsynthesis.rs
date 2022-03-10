// use crate::nftabuilder::{*};
// use crate::spec::{*};
// use crate::ntfa::{*};
// use crate::queue::{*};
// use std::collections::BinaryHeap;
// use std::collections::HashMap;
// use std::collections::HashSet;
// use std::cell::RefCell;
// use std::rc::Rc;
// use ProcValue::{*};
// use crate::debug::{*};
// use RefineLiteral::{*};
// use crate::synthesis::{extract_subexpressions};


// pub fn new_synthesize(
//     mut exprbuilder:ExpressionBuilder,
//     spec:SpecVariant,
//     input_type:usize,
//     output_type:usize
// ) {
//     let mut ntfabuilder = NTFABuilder::new(input_type,output_type);
//     let confirmer = spec.getconfirmer();
//     let mut heap = BinaryHeap::new();
//     heap.push(QueueElem{ item:spec, priority:0 });
//     while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
//         println!("popping!");
//         'specloop: while let Some(states) = spec.get_next() {
//             let mut graph_buffer : HashMap<usize,PartialNTFA> = HashMap::new();
//             let mut accepting_states : HashMap<usize,HashSet<(usize,TermClassification)>> = HashMap::new();
//             let mut opntfa : Option<usize> = None;
//             let mut subexpressions = extract_subexpressions(&mut exprbuilder,&states);
//             let mut order = states.keys().copied().collect::<Vec<_>>();
//             order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);
//             let mut debug_converted = Vec::new();
//             let mut debug_intersected = Vec::new();
//             for (interp,a) in order.into_iter().enumerate() {
//                 println!("building ntfa for: {:?}",DebugValue {
//                     t:a,
//                     expr:&exprbuilder
//                 });
//                 let newntfa = match ntfabuilder.build_ntfa(
//                     &mut exprbuilder,
//                     a,
//                     &states,
//                     &confirmer,
//                     &mut accepting_states,
//                     &mut graph_buffer,
//                     &mut subexpressions,
//                     10,interp
//                 ) {
//                     Some(z)=>z,
//                     _=>{
//                         //mark into omega
//                         panic!("No accepting states after ntfa built");
//                         if !spec.increment() {break 'specloop}
//                         continue 'specloop
//                     }
//                 };
//                 debug_converted.push(newntfa);
//                 opntfa = match opntfa {
//                     None=>Some(newntfa),
//                     Some(oldstate)=>{
//                         // println!("intersecting...");
//                         if let Some(intstate) = ntfabuilder.intersect(newntfa,oldstate,None).and_then(|u|{ntfabuilder.simplify(vec![u])})  {
//                             debug_intersected.push(intstate);
//                             Some(intstate)
//                         } else {
//                             //mark into omega
//                             panic!("No accepting states after intersection");
//                             if !spec.increment() {break 'specloop}
//                             continue 'specloop
//                         }
//                     }
//                 };
//             }
//             println!("generating accepting run!");
//             let ntfa = opntfa.unwrap();
//             let accrunlist = ntfabuilder.get_accepting_runs(ntfa,&mut exprbuilder);
//             if accrunlist.len()==0 {
//                 panic!("No accepting runs");
//                 if !spec.increment() {break 'specloop}
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






