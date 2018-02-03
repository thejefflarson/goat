extern crate error_chain;
#[macro_use]
extern crate pest;
#[macro_use]
extern crate pest_derive;
extern crate llvm_sys;

pub mod parser;
pub mod ast;
pub mod types;


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
