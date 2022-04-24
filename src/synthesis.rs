use crate::nftabuilder::{*};
use crate::spec::{*};
use crate::nfta::{*};
use crate::queue::{*};
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;
use crate::debug::{*};
use RefineLiteral::{*};
use std::mem::{take};


pub fn synthesize(
    mut exprbuilder:ExpressionBuilder,
    spec:SpecVariant,
    input_type:usize,
    output_type:usize
) {
    let mut subex : SubexpressionFinder = SubexpressionFinder::new();
    let mut nftabuilder = NFTABuilder::new(input_type,output_type);
    let confirmer = spec.getconfirmer();
    let mut heap = BinaryHeap::new();
    heap.push(QueueElem{ item:spec, priority:0 });
    while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
        println!("popping!");
        'specloop: for disjunct in spec.get_truesets().iter_mut() {
            let mut order = disjunct.states.keys().copied().collect::<Vec<_>>();
            order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);

            // let mut debug_converted = Vec::new();
            // let mut debug_intersected = Vec::new();
            for (interp,a) in order.into_iter().enumerate() {
                println!("building nfta for: {:?}",DebugValue {
                    t:a,
                    expr:&exprbuilder
                });
                let newnfta = nftabuilder.build_nfta(
                    &mut exprbuilder,
                    a,
                    &confirmer,
                    disjunct,
                    &mut subex,
                    100000,interp
                );
                if newnfta.len()==0 {
                    //mark into omega
                    println!("No accepting states after nfta built");
                    continue 'specloop
                }
                // debug_converted.push(newnfta);
                disjunct.opnfta = match take(&mut disjunct.opnfta) {
                    None=>Some(newnfta),
                    Some(oldstate)=>{
                        let intstate = nftabuilder.intersect(newnfta,oldstate,None);
                        if intstate.len()==0 {
                            //mark into omega
                            println!("No accepting states after intersection");
                            continue 'specloop
                        }
                        Some(intstate)
                    }
                };
            }
            println!("generating accepting run!");
            let nfta = disjunct.opnfta.clone().unwrap();
            // nftabuilder.output_tree(nfta);
            let (solution,solsize,witness) = nftabuilder.get_boring_accepting_run(nfta,&mut exprbuilder);
            let solution = solution.get_dsl(&exprbuilder);
            // let witness : Vec<(usize,usize)> = witness.into_iter().map(|((a,_),(b,_))|(a,b)).collect();
            println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);//
            // return;
            
            let dslsol = Rc::new(solution.clone());
            let tmemo = Rc::new(RefCell::new(HashMap::new()));
            if disjunct.states.iter().all(|(key,val)|{
                let relval = exprbuilder.eval_recursive_function(dslsol.clone(),tmemo.clone(),*key);
                // println!("f({:?}) = {:?}",DebugValue {
                //     t:*key,
                //     expr:&exprbuilder
                // },DebugValue {
                //     t:relval,
                //     expr:&exprbuilder
                // });
                relval != 0 && val.state.accepts(relval) && confirmer.accepts(&mut exprbuilder,*key,relval)
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
            let no_side = spec.refine_disjoint(&witness.iter().map(|(k,v)|(*k,NeqLit(*v))).collect::<Vec<_>>());
            let mut yes_side = spec;
            for (k,v) in witness {
                yes_side.refine(k,EqLit(v));
            }
            if no_side.is_valid() {
                heap.push(QueueElem{ item:no_side, priority:solsize });
            }
            if yes_side.is_valid() {
                heap.push(QueueElem{ item:yes_side, priority:solsize });
            }
            break 'specloop;
        }
    }
}






