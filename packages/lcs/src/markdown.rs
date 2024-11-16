use std::ops::Deref;

use colored::{Color, ColoredString};

pub trait Markdown {
    fn markdown(&self) -> String;
}

impl Markdown for ColoredString {
    fn markdown(&self) -> String {
        match self.fgcolor() {
            Some(color) => format!(
                "<span style=\"color: {};\">{}</span>",
                match color {
                    Color::Black => "black",
                    Color::Red => "red",
                    Color::Green => "green",
                    Color::Yellow => "yellow",
                    Color::Blue => "blue",
                    Color::Magenta => "magenta",
                    Color::Cyan => "cyan",
                    Color::White => "white",
                    _ => unimplemented!(),
                },
                self.deref()
            ),
            None => self.to_string(),
        }
    }
}
