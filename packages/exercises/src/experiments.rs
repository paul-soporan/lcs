use std::fs;

use lcs::propositional_logic::dimacs::DimacsCnf;

pub fn run() {
    let data = fs::read_to_string("test.cnf").unwrap();
    let dimacs_cnf = data.parse::<DimacsCnf>().unwrap();

    println!("{}", dimacs_cnf.cnf);
}
