
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

    fn to_string(&self, cardinality: usize, literal_mode: bool) -> String {
        let mut result: String = String::new();
        let mut literal: char = std::char::from_u32('A' as u32 + (cardinality - 1) as u32).unwrap();

        let mut value = self.value;
        let mut mask = self.mask;

        for _ in 0..cardinality {
            // literal mode (write the term using letters)
            if literal_mode {
                if mask & 1 == 0 {
                    result.insert(0, literal);
                    if value & 1 == 0 {
                        result.insert(1, '\'');
                    }
                }
            }

            // non literal mode (write the term in binary)
            if !literal_mode {
                if mask & 1 == 0 {
                    result.insert(0, if value & 1 == 0 { '0' } else { '1' });
                } else {
                    result.insert(0, '-');
                }
            }

            mask >>= 1;
            value >>= 1;

            literal = std::char::from_u32(literal as u32 - 1).unwrap();
        }

        return result
    }

    fn terms_to_string<'a>(cardinality: usize, terms: impl Iterator<Item = &'a Term>, literal_mode: bool) -> String {
        let mut result: String = terms.map(|term| -> String { term.to_string(cardinality, literal_mode) })
            .collect::<Vec<String>>()
            .join(",");

        result = format!("({})", result);

        return result
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
    /// Number of bits
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

pub fn qmc_find_prime_imp(f: &BinaryFunction, to_simplify: &HashSet<Term>) -> (HashSet<Term>, usize) {

    print!("[QMC] To simplify: {}\n", Term::terms_to_string(f.cardinality, to_simplify.iter(), false));

    let groups_num = f.cardinality + 1;
    let mut groups: Vec<Vec<(&Term, bool)>> = vec![Vec::new(); groups_num];
    for imp in to_simplify.iter() {
        let num_of_1 = f.get_number_of_1(imp.value, !imp.mask);
        groups[num_of_1].push((imp, false));
    }

    for num_of_1 in 0..groups_num {
        print!("[QMC] Group {}: {}\n", num_of_1, Term::terms_to_string(
            f.cardinality,
            groups[num_of_1].iter().map(|(term, _)| (*term)),
            false
        ));
    }

    let mut result: HashSet<Term> = HashSet::new();
    let mut simplified_num = 0;

    for i in 0..groups.len() {
        let j = i + 1;

        let (i_group, j_group) = groups.split_at_mut(j);

        for (imp_a, a_simplified) in i_group.last_mut().unwrap() {
            if j < groups_num {
                for (imp_b, b_simplified) in j_group.first_mut().unwrap() {
                    // The two implicants must share the same mask:
                    // 10-- | 00-- | -00-
                    // -001 | 01-- | -11-
                    // NO   | YES  | YES  ...
                    if imp_a.mask != imp_b.mask {
                        continue;
                    }

                    // Gets the differing 1s from both implicants, if the number of differing 1s is 1,
                    // then we can create a new simplified term.
                    // 10  | 00
                    // 01  | 01
                    // 11  | 01
                    // NO  | YES ...
                    let mask = imp_a.mask; // = imp_b.mask
                    let diff = imp_a.value ^ imp_b.value;
                    if f.get_number_of_1(diff, !mask) == 1 {
                        let simplified_imp = Term::new_with_mask(
                            imp_a.value,
                            mask | diff
                        );

                        result.insert(simplified_imp);

                        *a_simplified = true;
                        *b_simplified = true;
                    }
                }
            }

            // If the implicant hasn't been simplified put it in the resulting vector.
            // 000 | 00- | 00- | 00-
            // 001 |     | 001 | 001
            // 111 |     |     | 111
            // 001 couldn't get simplified because varies two 1s compared to 111.
            if !*a_simplified {
                result.insert((*imp_a).clone());
            } else {
                simplified_num += 1;
            }
        }
    }

    print!("[QMC] Simplified: {}\n", simplified_num);

    if simplified_num > 0 {
        result = qmc_find_prime_imp(f, &result).0;
    }

    return (result, simplified_num);
}

pub fn qmc_find_prime_imp_from_func(f: &BinaryFunction) -> HashSet<Term> {
    // Initially implicants are taken both from min_terms and dont_care, and they're cloned inside one single vector.
    let mut imp: HashSet<Term> = HashSet::new();
    imp.extend(f.terms.iter().cloned());
    imp.extend(f.dont_care.iter().cloned());

    return qmc_find_prime_imp(&f, &imp).0;
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

    f.add_dont_care(Term::new(9));
    f.add_dont_care(Term::new(14));

    let result = qmc_find_prime_imp_from_func(&f);

    print!("Result:\n");
    for implicant in result {
        print!("{}\n", implicant.to_string(f.cardinality, true));
    }
}
