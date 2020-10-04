/**
 * Classic RegExp implementation (NFA, DFA).
 *
 * by Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 * MIT License, 2017
 */

/**
 * Epsilon.
 */
const EPSILON = 'ε';

/**
 * Epsilon-closure.
 */
const EPSILON_CLOSURE = `${EPSILON}*`;

// -----------------------------------------------------------------------------
// Generic state class (used by NFA and DFA states).

/**
 * An state maintains a transition map on symbols,
 * and also the flag whether the state is accepting.
 */
class State {
  constructor({
    accepting = false,
  } = {}) {

    /**
     * Outgoing transitions to other states.
     */
    this._transitions = new Map();

    /**
     * Whether the state is accepting.
     */
    this.accepting = accepting;
  }

  /**
   * Returns transitions for this state.
   */
  getTransitions() {
    return this._transitions;
  }

  /**
   * Creates a transition on symbol.
   */
  addTransition(symbol, toState) {
    this.getTransitionsOnSymbol(symbol).add(toState);
    return this;
  }

  /**
   * Returns transitions set on symbol.
   */
  getTransitionsOnSymbol(symbol) {
    let transitions = this._transitions.get(symbol);

    if (!transitions) {
      transitions = new Set();
      this._transitions.set(symbol, transitions);
    }

    return transitions;
  }
}

// -----------------------------------------------------------------------------
// NFA state.

/**
 * NFA states works with epsilon-transitions.
 */
class NFAState extends State {

  /**
   * Whether this state matches a string.
   *
   * We maintain set of visited epsilon-states to avoid infinite loops
   * when an epsilon-transition goes eventually to itself.
   */
  matches(string, visited = new Set()) {
    // An epsilon-state has been visited, stop to avoid infinite loop.
    if (visited.has(this)) {
      return false;
    }

    visited.add(this);

    // No symbols left..
    if (string.length === 0) {
      // .. and we're in the accepting state.
      if (this.accepting) {
        return true;
      }

      // Check if we can reach any accepting state from
      // on the epsilon transitions.
      for (const nextState of this.getTransitionsOnSymbol(EPSILON)) {
        if (nextState.matches('', visited)) {
          return true;
        }
      }
      return false;
    }

    // Else, we get some symbols.
    const symbol = string[0];
    const rest = string.slice(1);

    const symbolTransitions = this.getTransitionsOnSymbol(symbol);
    for (const nextState of symbolTransitions) {
      if (nextState.matches(rest)) {
        return true;
      }
    }

    // If we couldn't match on symbol, check still epsilon-transitions
    // without consuming the symbol (i.e. continue from `string`, not `rest`).
    for (const nextState of this.getTransitionsOnSymbol(EPSILON)) {
      if (nextState.matches(string, visited)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Returns an ε-closure for this state:
   * self + all states following ε-transitions.
   */
  getEpsilonClosure() {
    if (!this._epsilonClosure) {
      const epsilonTransitions = this.getTransitionsOnSymbol(EPSILON);
      const closure = this._epsilonClosure = new Set();
      closure.add(this);
      for (const nextState of epsilonTransitions) {
        if (!closure.has(nextState)) {
          closure.add(nextState);
          const nextClosure = nextState.getEpsilonClosure();
          nextClosure.forEach(state => closure.add(state));
        }
      }
    }

    return this._epsilonClosure;
  }
}

// -----------------------------------------------------------------------------
// NFA.

/**
 * NFA fragment.
 *
 * NFA sub-fragments can be combined to a larger NFAs building
 * the resulting machine. Combining the fragments is done by patching
 * edges of the in- and out-states.
 *
 * 2-states implementation, `in`, and `out`. Eventually all transitions
 * go to the same `out`, which can further be connected via ε-transition
 * to other fragment.
 */
class NFA {
  constructor(inState, outState) {
    this.in = inState;
    this.out = outState;
  }

  /**
   * Tries to recognize a string based on this NFA fragment.
   */
  matches(string) {
    return this.in.matches(string);
  }

  /**
   * Returns alphabet for this NFA.
   */
  getAlphabet() {
    if (!this._alphabet) {
      this._alphabet = new Set();
      const table = this.getTransitionTable();
      for (const state in table) {
        const transitions = table[state];
        for (const symbol in transitions) if (symbol !== EPSILON_CLOSURE) {
          this._alphabet.add(symbol);
        }
      }
    }

    return this._alphabet;
  }

  /**
   * Returns set of accepting states.
   */
  getAcceptingStates() {
    if (!this._acceptingStates) {
      // States are determined during table construction.
      this.getTransitionTable();
    }

    return this._acceptingStates;
  }

  /**
   * Returns accepting state numbers.
   */
  getAcceptingStateNumbers() {
    if (!this._acceptingStateNumbers) {
      this._acceptingStateNumbers = new Set();
      for (const acceptingState of this.getAcceptingStates()) {
        this._acceptingStateNumbers.add(acceptingState.number);
      }
    }

    return this._acceptingStateNumbers;
  }

  /**
   * Builds and returns transition table.
   */
  getTransitionTable() {
    if (!this._transitionTable) {
      this._transitionTable = {};
      this._acceptingStates = new Set();

      const visited = new Set();
      const symbols = new Set();

      const visitState = (state) => {
        if (visited.has(state)) {
          return;
        }

        visited.add(state);
        state.number = visited.size;
        this._transitionTable[state.number] = {};

        if (state.accepting) {
          this._acceptingStates.add(state);
        }

        const transitions = state.getTransitions();

        for (const [symbol, symbolTransitions] of transitions) {
          let combinedState = [];
          symbols.add(symbol);
          for (const nextState of symbolTransitions) {
            visitState(nextState);
            combinedState.push(nextState.number);
          }
          this._transitionTable[state.number][symbol] = combinedState;
        }
      };

      // Traverse the graph starting from the `in`.
      visitState(this.in);

      // Append epsilon-closure column.
      visited.forEach(state => {
        delete this._transitionTable[state.number][EPSILON];
        this._transitionTable[state.number][EPSILON_CLOSURE] =
          [...state.getEpsilonClosure()].map(s => s.number);
      });
    }

    return this._transitionTable;
  }
}

// -----------------------------------------------------------------------------
// DFA.

/**
 * DFA is build by converting from NFA (subset construction).
 */
class DFA {
  constructor(nfa) {
    this._nfa = nfa;
  }

  /**
   * Returns alphabet for this DFA.
   */
  getAlphabet() {
    return this._nfa.getAlphabet();
  }

  /**
   * Returns starting state.
   */
  getStartingStateNumber() {
    if (!this._startingStateNumber) {
      // Starting state is determined during table construction.
      this.getTransitionTable();
    }

    return this._startingStateNumber;
  }

  /**
   * Returns accepting states.
   */
  getAcceptingStateNumbers() {
    if (!this._acceptingStateNumbers) {
      // Accepting states are determined during table construction.
      this.getTransitionTable();
    }

    return this._acceptingStateNumbers;
  }

  /**
   * DFA transition table is built from NFA table.
   */
  getTransitionTable() {
    if (this._transitionTable) {
      return this._transitionTable;
    }

    // Calculate from NFA transition table.
    const nfaTable = this._nfa.getTransitionTable();
    const nfaStates = Object.keys(nfaTable);

    this._startingStateNumber = 0;
    this._acceptingStateNumbers = new Set();

    // Start state of DFA is E(S[nfa])
    const startState = nfaTable[nfaStates[0]][EPSILON_CLOSURE];

    this._startingStateNumber = startState.join(',');

    // Init the worklist (states which should be in the DFA).
    const worklist = [startState];

    const dfaTable = {};

    while (worklist.length > 0) {
      const states = worklist.shift();
      const dfaStateLabel = states.join(',');
      dfaTable[dfaStateLabel] = {};

      this.getAlphabet().forEach(symbol => {
        let onSymbol = [];

        states.forEach(state => {
          const nfaStatesOnSymbol = nfaTable[state][symbol];
          if (!nfaStatesOnSymbol) {
            return;
          }

          nfaStatesOnSymbol.forEach(nfaStateOnSymbol => {
            if (!nfaTable[nfaStateOnSymbol]) {
              return;
            }
            onSymbol.push(...nfaTable[nfaStateOnSymbol][EPSILON_CLOSURE]);
          });

        });

        const dfaStatesOnSymbolSet = new Set(onSymbol);
        const dfaStatesOnSymbol = [...dfaStatesOnSymbolSet];

        if (dfaStatesOnSymbol.length > 0) {
          const dfaOnSymbolStr = dfaStatesOnSymbol.join(',');

          // Determine whether the combined state is accepting.
          const nfaAcceptingStates = this._nfa.getAcceptingStateNumbers();
          for (const nfaAcceptingState of nfaAcceptingStates) {
            // If any of the states from NFA is accepting, DFA's
            // state is accepting as well.
            if (dfaStatesOnSymbolSet.has(nfaAcceptingState)) {
              this._acceptingStateNumbers.add(dfaOnSymbolStr);
              break;
            }
          }

          dfaTable[dfaStateLabel][symbol] = dfaOnSymbolStr;

          if (!dfaTable.hasOwnProperty(dfaOnSymbolStr)) {
            worklist.unshift(dfaStatesOnSymbol);
          }
        }
      });

    }

    return (this._transitionTable = dfaTable);
  }

  /**
   * Checks whether this DFA accepts a string.
   */
  matches(string) {
    let state = this.getStartingStateNumber();
    let i = 0;
    const table = this.getTransitionTable();

    while (string[i]) {
      state = table[state][string[i++]];
      if (!state) {
        return false;
      }
    }

    if (!this.getAcceptingStateNumbers().has(state)) {
      return false;
    }

    return true;
  }
}


// -----------------------------------------------------------------------------
// Char NFA fragment: `c`

/**
 * Char factory.
 *
 * Creates an NFA fragment for a single char.
 *
 * [in] --c--> [out]
 */
function char(c) {
  const inState = new NFAState();
  const outState = new NFAState({
    accepting: true,
  });

  return new NFA(
    inState.addTransition(c, outState),
    outState
  );
}

// -----------------------------------------------------------------------------
// Epsilon NFA fragment

/**
 * Epsilon factory.
 *
 * Creates an NFA fragment for ε (recognizes an empty string).
 *
 * [in] --ε--> [out]
 */
function e() {
  return char(EPSILON);
}

// -----------------------------------------------------------------------------
// Alteration NFA fragment: `abc`

/**
 * Creates a connection between two NFA fragments on epsilon transition.
 *
 * [in-a] --a--> [out-a] --ε--> [in-b] --b--> [out-b]
 */
function altPair(first, second) {
  first.out.accepting = false;
  second.out.accepting = true;

  first.out.addTransition(EPSILON, second.in);
  first.out = second.in;

  return new NFA(first.in, second.out)
}

/**
 * Alteration factory.
 *
 * Creates a alteration NFA for (at least) two NFA-fragments.
 */
function alt(first, ...fragments) {
  for (let fragment of fragments) {
    first = altPair(first, fragment);
  }
  return first;
}

// -----------------------------------------------------------------------------
// Disjunction NFA fragment: `a|b`

/**
 * Creates a disjunction choice between two fragments.
 */
function orPair(first, second) {
  const inState = new NFAState();
  const outState = new NFAState();

  inState.addTransition(EPSILON, first.in);
  inState.addTransition(EPSILON, second.in);

  outState.accepting = true;
  first.out.accepting = false;
  second.out.accepting = false;

  first.out.addTransition(EPSILON, outState);
  second.out.addTransition(EPSILON, outState);

  return new NFA(inState, outState);
}

/**
 * Disjunction factory.
 *
 * Creates a disjunction NFA for (at least) two NFA-fragments.
 */
function or(first, ...fragments) {
  for (let fragment of fragments) {
    first = orPair(first, fragment);
  }
  return first;
}

// -----------------------------------------------------------------------------
// Kleene-closure

/**
 * Kleene star/closure.
 *
 * a*
 */
function rep(fragment) {
  const inState = new NFAState();
  const outState = new NFAState({
    accepting: true,
  });

  // 0 or more.
  inState.addTransition(EPSILON, fragment.in);
  inState.addTransition(EPSILON, outState);

  fragment.out.accepting = false;
  fragment.out.addTransition(EPSILON, outState);
  outState.addTransition(EPSILON, fragment.in);

  return new NFA(inState, outState);
}

// -----------------------------------------------------------------------------
// Examples:

// p: x|y
let nfa = or(char('x'), char('y'));

console.log('Pattern: x|y\n');

console.log('NFA transition table:\n');
console.log(nfa.getTransitionTable());
console.log('');

console.log('NFA accepting states:', nfa.getAcceptingStateNumbers());
console.log('');

console.log(' - NFA matches "x":', nfa.matches('x'));
console.log(' - NFA matches "y":', nfa.matches('y'));
console.log('');

const dfa = new DFA(nfa);

console.log('2. DFA transition table:\n');
console.log(dfa.getTransitionTable());
console.log('');

console.log('DFA accepting states:', dfa.getAcceptingStateNumbers());
console.log('');

console.log('x|y, DFA matches "x":', dfa.matches('x'));
console.log('x|y, DFA matches "y":', dfa.matches('y'));
