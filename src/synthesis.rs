use crate::nftabuilder::{*};
use crate::spec::{*};
use crate::ntfa::{*};
use crate::queue::{*};
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cell::RefCell;
use std::rc::Rc;
use ProcValue::{*};
use crate::debug::{*};
use RefineLiteral::{*};

pub fn extract_subexpressions(
    builder:&ExpressionBuilder,
    states:&HashMap<usize,BaseLiteral>
)->HashMap<usize,HashSet<usize>> {
    let mut subexpressions:HashMap<usize,HashSet<usize>> = HashMap::new();
    let mut stack : Vec<usize> = Vec::new();
    for key in states.keys() {
        if subexpressions.contains_key(key) {continue;}
        stack.push(*key);
        'ou: while let Some(x) = stack.last() {
            if subexpressions.contains_key(key) {continue;}
            match &builder.values[*x].0 {
                Const(_,z) if z.len()>0 => {
                    let mut bmap = Vec::new();
                    for a in z.iter() {
                        if let Some(ax) = subexpressions.get(&a) {bmap.push(ax);}
                        else {stack.push(*a);continue 'ou;}
                    }
                    let mut hm:HashSet<usize> = if z.len()==1 {bmap[0].clone()} else {bmap[0].union(&bmap[1]).copied().collect()};
                    for u in 2..bmap.len() {hm=hm.union(&bmap[u]).copied().collect()}
                    for a in z.iter() {hm.insert(*a);}
                    let x = stack.pop().unwrap();
                    subexpressions.insert(x,hm);
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
    let mut ntfabuilder = NTFABuilder::new(input_type,output_type);
    let confirmer = spec.getconfirmer();
    let mut heap = BinaryHeap::new();
    heap.push(QueueElem{ item:spec, priority:0 });
    while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
        println!("popping!");
        'specloop: while let Some(states) = spec.get_next() {
            let mut graph_buffer : HashMap<usize,PartialNTFA> = HashMap::new();
            let mut accepting_states : HashMap<usize,HashSet<(usize,TermClassification)>> = HashMap::new();
            let mut term_size_limiter : HashMap<usize,usize> = HashMap::new();
            let mut opntfa : Option<usize> = None;
            let mut subexpressions = extract_subexpressions(&mut exprbuilder,&states);
            let mut order = states.keys().copied().collect::<Vec<_>>();
            order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);
            let mut debug_converted = Vec::new();
            let mut debug_intersected = Vec::new();
            for (interp,a) in order.into_iter().enumerate() {
                println!("building ntfa for: {:?}",DebugValue {
                    t:a,
                    expr:&exprbuilder
                });
                let newntfa = match ntfabuilder.build_ntfa(
                    &mut exprbuilder,
                    a,
                    &states,
                    &confirmer,
                    &mut accepting_states,
                    &mut graph_buffer,
                    &mut subexpressions,
                    &mut term_size_limiter,
                    100000,interp
                ) {
                    Some(z)=>z,
                    _=>{
                        //mark into omega
                        println!("No accepting states after ntfa built");
                        if !spec.increment() {break 'specloop}
                        continue 'specloop
                    }
                };
                debug_converted.push(newntfa);
                opntfa = match opntfa {
                    None=>Some(newntfa),
                    Some(oldstate)=>{
                        // println!("intersecting...");
                        if let Some(intstate) = ntfabuilder.intersect(newntfa,oldstate,None).and_then(|u|{ntfabuilder.simplify(vec![u])})  {
                            debug_intersected.push(intstate);
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
            println!("generating accepting run!");
            let ntfa = opntfa.unwrap();
            // ntfabuilder.output_tree(ntfa);
            let (solution,solsize,witness) = ntfabuilder.get_boring_accepting_run(ntfa,&mut exprbuilder);
            println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);//
            // return;
            
            let dslsol = Rc::new(solution.clone());
            let tmemo = Rc::new(RefCell::new(HashMap::new()));
            if states.iter().all(|(key,val)|{
                let relval = exprbuilder.eval_recursive_function(dslsol.clone(),tmemo.clone(),*key);
                // println!("f({:?}) = {:?}",DebugValue {
                //     t:*key,
                //     expr:&exprbuilder
                // },DebugValue {
                //     t:relval,
                //     expr:&exprbuilder
                // });
                relval != 0 && val.accepts(relval) && confirmer.accepts(&mut exprbuilder,*key,relval)
            }) {
                println!("SOLUTION FOUND!");
                return;
            }

            println!("witness:");
            for (k,v) in witness.iter() {
                println!("\tf({:?}) = {:?}",DebugValue {
                    t:*k,
                    expr:&exprbuilder
                },DebugValue {
                    t:*v,
                    expr:&exprbuilder
                });
            }
            // return;

            let mut yes_side = spec.clone();
            let mut is_yes_ok = true;
            let disj : Vec<_> = witness.into_iter().map(|(k,v)|{
                is_yes_ok = is_yes_ok && yes_side.refine(k,EqLit(v));
                (k,NeqLit(v))
            }).collect();
            if is_yes_ok {
                heap.push(QueueElem{ item:yes_side, priority:solsize });
            }
            if spec.refine_disjoint(disj) {
                heap.push(QueueElem{ item:spec, priority:solsize });
            }
            break;
        }
    }
}






