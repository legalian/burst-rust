

#![allow(dead_code)]
mod mlsparser;
mod ntfa;
mod nftabuilder;
mod cluster;
mod graph;
mod queue;
mod spec;
mod dsl;
mod debug;
mod synthesis;

use std::ffi::OsStr;
use std::fs::read_dir;
use dsl::interpret_file;
use synthesis::synthesize;
use std::path::PathBuf;


fn main() {
    println!("there might be an argument for intersecting with all the hidden trees...");
    println!("just because you found a solution doesn't mean that it's the smallest solution of that branch.");
    println!("you'll need to further refine your answer before you output it.");
    // println!("")


    println!("");
    println!("make simplification occur in-place???????? (this could potentially be non-optimal, because which revhash entry is relevant now?)");
    println!("to answer that, keep in mind that there's only a revhash if you have a concrete entry with no loopbacks, and those can be simplified in-place as they are built.");
    println!("so the placeholder one doesn't simplify in place, but does check to see if an instantiation of this already exists");
    println!("");
    println!("when building, keep an itenerary alongside the memo to know which things are closed if all children get closed, mark yourself closed when you finish.");
    println!("Then, if you marked your thing as closed, deeply simplify yourself and do the full lookup, storing the placeholder you reserved, and marking the result as completely simplified.");
    println!("in the minification routine that follows, given that you don't try ones that are already completely simplified, nothing you simplify will have a revhash, so you can simplify in place.");
    println!("UPDATE: it actually is beneficial for unclosed ids to be contained in the revhash, and furthermore it is beneficial for their unsimplified versions to point to the final version in the revhash, but why stop there? do both.");
    println!("");
    println!("you need to make sure that simplification can completely simplify something in one pass, treating encountered ACTIVE as CLOSED.");
    println!("the only problem I can see is calculating the union of that thing with another thing, but the union would automatically be counted as unclosed so whatever");
    println!("");
    println!("you need to revisit the needs_simplification routine for the non-concrete branch. See if it's possible for it to do its job, seeing as it needs to be run on the recursive branch, and one of its criterea is that no children may require simplification. ");
    println!("good chance that that is just not a thing anymore. (until more advanced work is done)");
    println!("");
    println!("ought to release unused placeholders back into the pool with a cluster data structure.");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("ok so now you have a new approach based on having a simplification queue. Here's where it misses(potentially):");
    println!("it's possible that you miss sharing opportunities because the revhash only contains the unsimplified versions UNTIL after construction is over.");
    println!("");
    println!("");
    println!("simplify singular alim, blim");
    println!("");
    println!("");

    println!("the de brujin method can have a really cool simplification opportunity depending on how you treat 0. the obvious way would incorporate it, but if you don't, you can reroll yourself thinner");



    let mut paths : Vec<PathBuf> = read_dir("evaluation/benchmarks/io").unwrap().into_iter().chain(
        read_dir("evaluation/benchmarks/logical").unwrap().into_iter()).chain(
            read_dir("evaluation/benchmarks/ref").unwrap().into_iter()).filter_map(|x|{
                let p = x.unwrap().path();
                if p.extension().and_then(OsStr::to_str)==Some("decls") {None}
                else {Some(p)}
            }).collect();
    paths.sort();
    for fullpath in paths.into_iter().take(1) {
        let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
        synthesize(builder,spec,input_type,output_type);
    }
    // for fullpath in paths.into_iter().skip(7).take(1) {
    //     let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
    //     synthesize(builder,spec,input_type,output_type);
    // }
}







