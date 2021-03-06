use crate::nftabuilder::{*};
use crate::spec::{*};
use crate::ntfa::{*};
use crate::queue::{*};
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
// use std::rc::Rc;
use ProcValue::{*};
// use ProcType::{*};
// use RefineLiteral::{*};
use crate::debug::{*};
use crate::ntfa::{*};


fn extract_subexpressions(
    builder:&ExpressionBuilder,
    states:&HashMap<usize,BaseLiteral>
)->HashMap<usize,HashSet<usize>> {
    let mut subexpressions:HashMap<usize,HashSet<usize>> = HashMap::new();
    let mut stack : Vec<usize> = Vec::new();
    for key in states.keys() {
        if subexpressions.contains_key(key) {continue;}
        stack.push(*key);
        while let Some(x) = stack.last() {
            if subexpressions.contains_key(key) {continue;}
            match &builder.values[*x].0 {
                PairValue(a,b)=>{
                    if let Some(ax) = subexpressions.get(&a) {
                        if let Some(bx) = subexpressions.get(&b) {
                            let mut hm:HashSet<usize> = ax.union(bx).copied().collect();
                            hm.insert(*a);hm.insert(*b);
                            let x = stack.pop().unwrap();
                            subexpressions.insert(x,hm);
                        } else {stack.push(*b)}
                    } else {stack.push(*a)}
                }
                LValue(a)|RValue(a)=>{
                    if let Some(ax) = subexpressions.get(&a) {
                        let mut hm = ax.clone();hm.insert(*a);
                        let x = stack.pop().unwrap();
                        subexpressions.insert(x,hm);
                    } else {stack.push(*a)}
                }
                _=>{
                    subexpressions.insert(*x,HashSet::new());
                    stack.pop();
                }
            }
        }
    } subexpressions
}


pub fn synthesize(
    mut exprbuilder:ExpressionBuilder,
    spec:SpecVariant,
    input_type:usize,
    output_type:usize
) {
    let mut ntfabuilder = NTFABuilder::new(&mut exprbuilder);
    let confirmer = spec.getconfirmer();
    let mut heap = BinaryHeap::new();
    heap.push(QueueElem{ item:spec, priority:0 });
    while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
        'specloop: while let Some(states) = spec.get_next() {
            println!("Found one option");
            let mut graph_buffer : HashMap<usize,Option<(usize,ValueMapper)>> = HashMap::new();
            let mut accepting_states : HashMap<usize,HashSet<usize>> = HashMap::new();
            let mut opntfa : Option<usize> = None;
            let mut tables : Vec<ValueMapper> = Vec::new();
            let mut subexpressions = extract_subexpressions(&mut exprbuilder,&states);
            let mut order = states.keys().copied().collect::<Vec<_>>();
            order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);
            for a in order {
                println!("Evaluating one literal");
                let (newntfa,newmapping) = match ntfabuilder.build_ntfa(
                    &mut exprbuilder,
                    a,input_type,
                    &states,output_type,
                    &confirmer,
                    &mut accepting_states,
                    &mut graph_buffer,
                    &mut subexpressions,
                    8
                ) {
                    Some(z)=>z,
                    None=>{
                        //mark into omega
                        println!("No accepting states after ntfa built");
                        if !spec.increment() {break 'specloop}
                        continue 'specloop
                    }
                };
            // for (newntfa,newmapping) in vec![{
            //     let mut res = PartialNTFA::new();
            //     res.add_rule(0,vec![],1);
            //     res.add_rule(1,vec![],1);

            //     res.add_rule(9,vec![1,0,1],3);
            //     println!("builing! {:?}",res);
            //     // res.add_rule(9,vec![2,2,0],3);
            //     res
            // }.convert(&mut ntfabuilder,&{let mut h = HashSet::new();h.insert(3);h}).unwrap(),{
            //     let mut res = PartialNTFA::new();
            //     res.add_rule(0,vec![],1);
            //     res.add_rule(1,vec![],2);

            //     // res.add_rule(9,vec![1,0,1],3);
            //     res.add_rule(9,vec![2,2,0],3);
            //     println!("builing! {:?}",res);
            //     res
            // }.convert(&mut ntfabuilder,&{let mut h = HashSet::new();h.insert(3);h}).unwrap(),] {


                println!("built!");
                ntfabuilder.output_tree(newntfa);
                tables.push(newmapping);
                opntfa = match opntfa {
                    None=>Some(newntfa),
                    Some(oldstate)=>{
                        println!("intersecting...");
                        if let (_,Some(intstate),_) = ntfabuilder.intersect(newntfa,oldstate) {
                            println!("outputting!");
                            ntfabuilder.output_tree(intstate);
                            // ntfabuilder.deplete_minification_queue();
                            // ntfabuilder.forget_minification_queue();
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






