use crate::nftabuilder::{*};
use crate::spec::{*};
use crate::ntfa::{*};
use crate::queue::{*};
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;
// use ProcValue::{*};
use RefineLiteral::{*};
use crate::debug::{*};

fn determine_visit_order(_builder:&ExpressionBuilder,states:&HashMap<usize,BaseLiteral>)->Vec<usize> {
    states.keys().copied().collect()
    // let mut visited : HashSet<usize> = HashSet::new();
    // let mut stack : Vec<usize> = Vec::new();
    // let mut order : Vec<usize> = Vec::new();
    // for key in states.keys() {
    //     if visited.contains(key) {continue;}
    //     stack.push(*key);
    //     while let Some(x) = stack.last() {
    //         if visited.contains(key) {continue;}
    //         match &builder.values[*x].0 {
    //             PairValue(a,b)=>{
    //                 if !visited.contains(&a) {stack.push(*a)}
    //                 else if !visited.contains(&b) {stack.push(*b)}
    //                 else {visited.insert(*x);order.push(*x);stack.pop();}
    //             }
    //             LValue(a)|RValue(a)=>{
    //                 if !visited.contains(a) {stack.push(*a)}
    //                 else {visited.insert(*x);order.push(*x);stack.pop();}
    //             }
    //             _=>{visited.insert(*x);order.push(*x);stack.pop();}
    //         }
    //     }
    // } order
}


pub fn synthesize(
    mut exprbuilder:ExpressionBuilder,
    spec:SpecVariant,
    input_type:usize,
    output_type:usize
) {
    let mut ntfabuilder = NTFABuilder::new();
    let confirmer = spec.getconfirmer();
    let mut heap = BinaryHeap::new();
    heap.push(QueueElem{ item:spec, priority:0 });
    while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
        'specloop: while let Some(states) = spec.get_next() {
            println!("Found one option");
            let order = determine_visit_order(&exprbuilder,&states);
            let mut accepting_states : HashMap<usize,HashSet<usize>> = HashMap::new();
            let mut opntfa : Option<usize> = None;
            let mut tables : Vec<ValueMapper> = Vec::new();
            for a in order {
                println!("Evaluating one literal");
                let (newstate,newaccepting) = ntfabuilder.build_ntfa(
                    &mut exprbuilder,
                    a,input_type,
                    &states,output_type,
                    &confirmer,
                    &mut accepting_states,
                    7
                );
                if newstate.is_none() {
                    //mark into omega
                    println!("No accepting states after ntfa built");
                    if !spec.increment() {break 'specloop}
                    continue 'specloop
                }
                // println!("just built ntfa: {:#?} {:?}",newstate,AcceptingStates{s:&newaccepting});
                let (newntfa,newmapping) = newstate.unwrap();
                accepting_states.insert(a,newaccepting);
                tables.push(newmapping);
                opntfa = match opntfa {
                    None=>Some(newntfa),
                    Some(oldstate)=>{
                        if let Some(intstate) = ntfabuilder.intersect(newntfa,oldstate) {
                            // println!("just intersected ntfa: {:#?} {:?}",intstate,AcceptingStates{s:&intacc});
                            Some(intstate)
                        } else {
                            //mark into omega
                            println!("No accepting states after intersection");
                            if !spec.increment() {break 'specloop}
                            continue 'specloop
                        }
                    }
                };
            }
            let ntfa = opntfa.unwrap();
            let solution_list = ntfabuilder.get_accepting_run(ntfa,&mut exprbuilder,&tables);
            if solution_list.len()>0 {
                for (solution,solsize,witness) in solution_list {
                    println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);
                }
                return;
                // let mut yes_side = spec.clone();
                // let mut is_yes_ok = true;
                // let disj : Vec<_> = witness.into_iter().map(|(k,v)|{
                //     is_yes_ok = is_yes_ok && yes_side.refine(k,EqLit(v));
                //     (k,NeqLit(v))
                // }).collect();
                // if is_yes_ok {
                //     heap.push(QueueElem{ item:yes_side, priority:solsize });
                // }
                // if spec.refine_disjoint(disj) {
                //     heap.push(QueueElem{ item:spec, priority:solsize });
                // }
                // break;
            } else {
                println!("accepting run failed. {:#?}",ntfa);
                if !spec.increment() {break 'specloop}
                continue 'specloop
            }
        }
    }
}






