/**
 * NFA (Non-deterministic finite automata)
 *
 * A formalism for regular grammars (to recognize strings based on regular
 * expressions).
 *
 * Regexp parser to transform AST to NFA:
 * https://www.npmjs.com/package/regexp-tree
 *
 * NFA/DFA fragment examples:
 * https://lambda.uta.edu/cse5317/notes/node9.html
 *
 * Some implementation based on:
 * http://matt.might.net/articles/implementation-of-nfas-and-regular-expressions-in-java/
 *
 * by Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 * MIT License, 2017
 */

/**
 * Epsilon.
 */
const EPSILON = 'ε';

// A convenient method for debugging set elements.
Set.prototype.get = function(index) {
  return [...this][index];
};

// -----------------------------------------------------------------------------
// NFA state.

/**
 * An NFA state maintains a transition map (on symbols, and epsilon),
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

  /**
   * Does a transition on symbol (with default index 0 if not passed).
   */
  goto(symbol, index = 0) {
    return this.getTransitionsOnSymbol(symbol).get(index);
  }

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
  const inState = new State();
  const outState = new State({
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
  const inState = new State();
  const outState = new State();

  inState.addTransition(EPSILON, first.in);
  inState.addTransition(EPSILON, second.in);

  outState.accepting = true;

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
  const inState = new State();
  const outState = new State({
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

const a = char('a');

// true
console.log(
  a.in
    .goto('a')
    .accepting
);

const b = char('b');
const c = char('c');

// abc
const abc = alt(a, b, c);

const path = abc.in
  .goto('a')
  .goto(EPSILON)
  .goto('b')
  .goto(EPSILON)
  .goto('c');

// true
console.log(path === c.out);

// a|b|c
const aORbORc = or(char('a'), char('b'), char('c'));

// true
console.log(
  aORbORc.in
    .goto(EPSILON, 1)
    .goto('c')
    .accepting
);

// a*
const aStar = rep(char('a'));

// Repeat `aa` string, true:
console.log(
  aStar.in
    .goto(EPSILON)
    .goto('a')
    .goto(EPSILON)
    .goto(EPSILON)
    .goto('a')
    .goto(EPSILON)
    .accepting
);

// Match `aaa` string on `a*` pattern:
console.log(aStar.matches('aaa'));
console.log(aStar.matches(''));

// -----------------------------------------------------------------------------
// Exercises:

// 1. Implement NFA transition table.
//
// 2. Implement NFA to DFA conversion + DFA transition table.
