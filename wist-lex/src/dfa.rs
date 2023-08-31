use crate::regex::{Regex, Set};

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct DFA<const N: usize> {
    pub start_state: [Regex; N],
    pub states: HashSet<[Regex; N]>,
    pub transitions: HashMap<[Regex; N], Vec<(Set, [Regex; N])>>,
}

impl<const N: usize> DFA<N> {
    pub fn from_regexes(regexes: [Regex; N]) -> Self {
        if N == 0 {
            panic!("DFA cannot be constructed from 0 regular expressions.")
        }

        let mut dfa = DFA {
            start_state: regexes.clone(),
            states: HashSet::new(),
            transitions: HashMap::new(),
        };

        dfa.states.insert(dfa.start_state.clone());

        dfa.explore(&dfa.start_state.clone());
        let empty_state: [Regex; N] = (0..N)
            .map(|_| crate::EMPTY_REGEX.clone())
            .collect::<Vec<Regex>>()
            .try_into()
            .unwrap();

        dfa.transitions.remove(&empty_state);

        dfa
    }

    fn explore(&mut self, state: &[Regex; N]) {
        let mut classes = Vec::new();
        for regex in state {
            let new_classes = regex.derivative_classes();
            classes.push(new_classes)
        }
        let mut sets = classes.pop().unwrap();
        for class in classes {
            let mut new_sets = HashSet::new();
            for l_set in &sets {
                for r_set in &class {
                    new_sets.insert(l_set.intersection(r_set));
                }
            }
            sets = new_sets;
        }

        for set in sets {
            self.goto(state, set);
        }
    }

    // Requires testing
    fn goto(&mut self, state: &[Regex; N], set: Set) {
        let c = set.get_symbol();
        let new_state = state.clone().map(|regex| regex.derivative(c));

        match self.transitions.get_mut(state) {
            Some(transitions) => transitions.push((set, new_state.clone())),
            None => {
                self.transitions
                    .insert(state.clone(), vec![(set, new_state.clone())]);
            }
        }

        if self.states.contains(&new_state) {
            return;
        } else {
            self.states.insert(new_state.clone());
            self.explore(&new_state);
        }
    }
}
