#![feature(const_generics)]

use std::mem::size_of;
use std::vec::Vec;
use std::cmp::Ordering;
use std::cmp::Ordering::{Less, Greater, Equal};
use std::hash::Hash;
use std::collections::HashSet;

#[inline]
pub fn get_bit(mut value: u32, pos: u32) -> bool {
    value = value >> pos;
    (value & 0x1) != 0
}

#[derive(Eq, PartialEq, Hash)]
pub struct Term {
    value: u32,

    /// The mask indicates if the bit at the i position should be considered or not.
    /// The mask bits are inverted for convenience.
    ///
    /// data: 1011
    /// mask: 0001
    /// This combination refers to the min_term AB'C.
    mask: u32,
}

impl Term {
    pub fn new_with_mask(value: u32, mask: u32) -> Term {
        Term { value, mask }
    }

    pub fn new(value: u32) -> Term {
        Term::new_with_mask(value, 0)
    }
}

impl Clone for Term {
    fn clone(&self) -> Self {
        Term {
            value: self.value,
            mask: self.mask
        }
    }
}

pub struct BinaryFunction {
    cardinality: usize,

    terms: HashSet<Term>,
    dont_care: HashSet<Term>
}

impl BinaryFunction {
    pub fn new(cardinality: usize) -> BinaryFunction {
        BinaryFunction {
            cardinality,
            terms: HashSet::new(),
            dont_care: HashSet::new()
        }
    }

    pub fn add_term(&mut self, term: Term) {
        self.terms.insert(term);
    }

    pub fn get_terms(&self) -> &HashSet<Term> {
        &self.terms
    }

    pub fn add_dont_care(&mut self, term: Term) {
        self.dont_care.insert(term);
    }

    pub fn get_dont_care(&self) -> &HashSet<Term> {
        &self.dont_care
    }

    fn to_string(&self, term: &Term) -> String {
        let mut symbol_char = 'A';
        let mut symbols = vec![];

        let mut i = (self.cardinality - 1) as u32;
        loop {
            let mut symbol = String::new();
            if !get_bit(term.mask, i) {
                symbol.push(symbol_char);
                if !get_bit(term.value, i) {
                    symbol += "'";
                }
            }
            symbols.push(symbol);

            symbol_char = std::char::from_u32((symbol_char as u32) + 1).unwrap();

            if i == 0 { break; }
            i -= 1;
        }

        symbols.join(",");

        format!("value={:#032b} mask={:#032b}", term.value, term.mask)
    }

    fn print_implicants(&self, implicants: &HashSet<Term>) {
        for implicant in implicants {
            print!("value={:#08b} mask={:#08b}\n", implicant.value, implicant.mask);
        }
    }

    /// Gets the number of 1s of the given value counting only the bits that
    /// corresponds to a set mask.
    fn get_number_of_1(&self, mut value: u32, mut mask: u32) -> usize {
        let mut result = 0;
        while value != 0 {
            if (mask & 1) != 0 && (value & 1) != 0 {
                result += 1;
            }
            value = value >> 1;
            mask = mask >> 1;
        }
        result
    }
}


pub fn find_prime_implicants(f: &BinaryFunction, implicants: &HashSet<Term>, step: u32) -> HashSet<Term> {
    // Implicants are grouped by the number of 1s they contain and referenced by the following structure.
    let group_count = f.cardinality + 1;
    let mut grouped_implicants: Vec<Vec<&Term>> = vec![Vec::new(); group_count];

    for implicant in implicants.iter() {
        grouped_implicants[f.get_number_of_1(implicant.value, !implicant.mask)].push(implicant);
    }

    let mut resulting_implicants: HashSet<Term> = HashSet::new();
    let mut has_ever_simplified = false;

    let debug = false;

    if debug {
        print!("Input:\n");
        f.print_implicants(implicants);

        print!("Groups:\n");
        for i in 0..grouped_implicants.len() {
            print!("Group {}\n", i);
            for implicant in &grouped_implicants[i] {
                print!("{}\n", f.to_string(&implicant));
            }
        }
    }

    for i in 0..grouped_implicants.len() {
        // Compares the implicants of the current group `i` with the next one `j`.
        let mut j = i + 1;

        // If `i` is pointing to the last group, as a second group, we check the previous.
        // This is done not to forget the last implicants.
        let last_group = j == grouped_implicants.len();
        if last_group {
            j = i - 1;
        }

        for implicant_a in &grouped_implicants[i] {
            let mut simplified = false;

            for implicant_b in &grouped_implicants[j] {
                // The two implicants must share the same mask:
                // 10-- | 00-- | -00-
                // -001 | 01-- | -11-
                // NO   | YES  | YES  ...
                if implicant_a.mask != implicant_b.mask {
                    continue;
                }

                // Gets the differing 1s from both implicants, if the number of differing 1s is 1,
                // then we can create a new simplified term.
                // 10  | 00
                // 01  | 01
                // 11  | 01
                // NO  | YES ...
                let mask = implicant_a.mask;
                let diff = implicant_a.value ^ implicant_b.value;
                if f.get_number_of_1(diff, !mask) == 1 {
                    // The last group shouldn't push already added implicants because they've already been added.
                    if !last_group {
                        let term = Term::new_with_mask(
                            implicant_a.value,
                            mask | diff
                        );
                        resulting_implicants.insert(term);

                    }
                    simplified = true;
                }
            }

            // If the implicant hasn't been simplified put it in the resulting vector.
            // 000 | 00- | 00- | 00-
            // 001 |     | 001 | 001
            // 111 |     |     | 111
            // 001 couldn't get simplified because varies two 1s compared to 111.
            if !simplified {
                resulting_implicants.insert((*implicant_a).clone());
            }

            has_ever_simplified |= simplified;
        }
    }

    if debug {
        print!("Result\n");
        f.print_implicants(&resulting_implicants);
    }

    // Has the program ever simplified something? If so, we can repeat this step.
    if has_ever_simplified {
        resulting_implicants = find_prime_implicants(f, &resulting_implicants, step + 1);
    }

    return resulting_implicants;
}

pub fn find_prime_implicants_from_function(f: &BinaryFunction) -> HashSet<Term> {
    // Initially implicants are taken both from min_terms and dont_care,
    // and they're clone inside one single vector.
    let mut implicants: HashSet<Term> = HashSet::new();
    implicants.extend(f.terms.iter().cloned());
    implicants.extend(f.dont_care.iter().cloned());

    return find_prime_implicants(&f, &implicants, 0);
}

fn main() {
    // Definition of the min terms and dont care.

    let mut f = BinaryFunction::new(4);
    f.add_term(Term::new(4));
    f.add_term(Term::new(8));
    f.add_term(Term::new(10));
    f.add_term(Term::new(11));
    f.add_term(Term::new(12));
    f.add_term(Term::new(15));

    f.add_term(Term::new(9));
    f.add_term(Term::new(14));

    let result = find_prime_implicants_from_function(&f);

    print!("Result:\n");
    for implicant in result {
        print!("{}\n", f.to_string(&implicant));
    }
}
