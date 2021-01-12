
use std::mem::size_of;
use std::vec::Vec;
use std::cmp::Ordering;
use std::cmp::Ordering::{Less, Greater, Equal};
use std::hash::Hash;
use std::collections::HashSet;
use std::borrow::BorrowMut;

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
    /// This combination refers to the min_term 101- or AB'C.
    mask: u32,
}

impl Term {
    pub fn new_with_mask(value: u32, mask: u32) -> Term {
        Term { value, mask }
    }

    pub fn new(value: u32) -> Term {
        Term::new_with_mask(value, 0)
    }

    pub fn covers(&self, term: &Term) -> bool {
        let common_mask = self.mask | term.mask;
        self.value & !common_mask == term.value & !common_mask
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

pub fn qmc_dominance_crit(rows: &mut HashSet<Term>, cols: &HashSet<Term>, covers: impl Fn(&Term, &Term) -> bool) -> usize {
    let mut to_del_rows: HashSet<Term> = HashSet::new();

    for row_1 in rows.iter() {
        for row_2 in rows.iter() {
            let was_del = to_del_rows.contains(row_1) || to_del_rows.contains(row_2); // One of the rows was simplified before!
            if !was_del && row_1 != row_2 {
                // row_1 is the one considered dominant.
                // row_2 is the one to check against.

                let mut is_dominant = true;
                for col in cols.iter() {
                    if !covers(row_1, col) && covers(row_2, col) {
                        is_dominant = false; // The row can't be dominant in this case.
                        break;
                    }
                }

                if is_dominant {
                    to_del_rows.insert(row_2.clone());
                }
            }
        }
    }

    for to_del_row in to_del_rows.iter() {
        rows.remove(to_del_row);
    }

    to_del_rows.len()
}

pub fn qmc_essentiality_crit(rows: &mut HashSet<Term>, cols: &mut HashSet<Term>) -> HashSet<Term> {
    let mut to_del_rows: HashSet<Term> = HashSet::new();
    let mut to_del_cols: HashSet<Term> = HashSet::new();

    let mut result = HashSet::new();

    for col in cols.iter() {
        if to_del_cols.contains(col) {
            continue;
        }

        for row_1 in rows.iter() {
            if to_del_rows.contains(row_1) {
                continue;
            }

            // Check if the current column is covered only by the row_1.
            let mut is_covered_only_by_me = row_1.covers(col);

            if is_covered_only_by_me {
                for row_2 in rows.iter() {
                    if to_del_rows.contains(row_2) {
                        continue;
                    }

                    if row_1 != row_2 && row_2.covers(col) {
                        is_covered_only_by_me = false;
                        break;
                    }
                }
            }

            // Remove the row and all the cols it covers from the given `rows` and `cols`.
            if is_covered_only_by_me {
                result.insert(row_1.clone());

                to_del_rows.insert(row_1.clone());
                for col in cols.iter() {
                    if row_1.covers(col) {
                        to_del_cols.insert(col.clone()); // Try to insert it even if it could be already there.
                    }
                }
            }
        }
    }

    for to_del_row in to_del_rows {
        rows.remove(&to_del_row);
    }

    for to_del_col in to_del_cols {
        cols.remove(&to_del_col);
    }

    result
}

pub fn qmc_find_essential_imp(f: &BinaryFunction, prime_imp: &HashSet<Term>) -> HashSet<Term> {
    let mut rows = prime_imp.clone();
    let mut cols = f.terms.clone();

    let mut result = HashSet::new();

    loop {
        // Using just the essentiality crit is enough to get the essential implicants.
        // The row/col dominant crit could be used but _just one_ of them, not both in the same process.
        /*
        loop {
            let mut simplified = false;
            simplified |= qmc_dominance_crit(&mut rows, &cols, |row, col| row.covers(col)) > 0; // Just use row dominance crit.
            //simplified |= qmc_dominance_crit(&mut cols, &rows, |col, row| row.covers(col)) > 0;
            if !simplified {
                break;
            }
        }
         */

        let found = qmc_essentiality_crit(&mut rows, &mut cols);
        if found.is_empty() {
            break;
        }
        result.extend(found);
    }

    result
}

pub fn qmc_simplify(f: &BinaryFunction) -> HashSet<Term> {
    let prime_imp = qmc_find_prime_imp_from_func(f);
    print!("[QMC] Prime implicants: {}\n", Term::terms_to_string(f.cardinality, prime_imp.iter(), false));

    let essential_imp = qmc_find_essential_imp(f, &prime_imp);
    print!("[QMC] Essential implicants: {}\n", Term::terms_to_string(f.cardinality, essential_imp.iter(), false));

    return essential_imp;
}

fn main() {
    // Definition of the binary function:
    let mut f = BinaryFunction::new(4); // The `cardinality` tells how many inputs do we have.

    // Here define the inputs combination that will give f(input) = 1.
    // Giving in f.add_term(5), will result in f(0101) = 1. Not defined inputs will result in f(not_def_input) = 0.
    f.add_term(Term::new(5));
    f.add_term(Term::new(6));
    f.add_term(Term::new(7));
    f.add_term(Term::new(8));

    // Here define the inputs combination that will give f(input) = x (or dont_care).
    // Giving in f.add_term(10), will result in f(1010) = x.
    f.add_dont_care(Term::new(10));
    f.add_dont_care(Term::new(11));

    // This is the function that will execute the algorithm and takes care of printing the results.
    qmc_simplify(&f);
}
