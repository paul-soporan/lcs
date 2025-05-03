#![feature(internal_output_capture)]
use std::{env, fs::File, io::Write, sync::Arc};

use filepath::FilePath;

mod experiments;
mod homework;

fn main() -> std::io::Result<()> {
    std::io::set_output_capture(Some(Default::default()));

    let hw_number = env::args()
        .nth(1)
        .expect("Please specify which homework to solve (1-10).")
        .parse::<u32>()
        .expect("Please specify a valid number.");

    match hw_number {
        0 => experiments::run(),
        1 => homework::hw_1::run(),
        2 => homework::hw_2::run(),
        3 => homework::hw_3::run(),
        4 => homework::hw_4::run(),
        5 => homework::hw_5::run(),
        6 => homework::hw_6::run(),
        7 => homework::hw_7::run(),
        8 => homework::hw_8::run(),
        9 => homework::hw_9::run(),
        10 => homework::hw_10::run(),
        _ => unimplemented!(),
    }

    let captured = std::io::set_output_capture(None).unwrap();

    let captured = Arc::try_unwrap(captured).unwrap();
    let captured = captured.into_inner().unwrap();

    let mut file = File::create("output.md")?;

    file.write_all(&captured)?;

    println!("Solved homework {}.", hw_number);

    println!(
        "Output written to {}.",
        file.path().unwrap().to_string_lossy()
    );

    Ok(())
}
