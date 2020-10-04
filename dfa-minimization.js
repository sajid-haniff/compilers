/**
 * DFA minization.
 *
 * A DFA table is minimized using N-equivalence algorithm.
 *
 * by Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

/**
 * Non-minizied DFA table for `/a|b/`.
 */
let table = {
  1: {a: 2, b: 3},
  2: {},
  3: {},
};

/**
 * Set of accepting states.
 */
const accepting = new Set([2, 3]);

/**
 * Alphabet.
 */
const alphabet = new Set(['a', 'b']);

/**
 * Map from state to current set it goes.
 */
let currentTransitionMap = {};

/**
 * Takes a DFA table, and returns a minimized version of it
 * compressing some states to groups (using standard, 0-, 1-,
 * 2-, ... N-equivalence algorithm).
 */
function minimize(table) {
  const allStates = Object.keys(table);

  const nonAccepting = new Set();

  allStates.forEach(state => {
    state = Number(state);
    const isAccepting = accepting.has(state);

    if (isAccepting) {
      currentTransitionMap[state] = accepting;
    } else {
      nonAccepting.add(state);
      currentTransitionMap[state] = nonAccepting;
    }
  });

  // ---------------------------------------------------------------------------
  // Step 1: build equivalent sets.

  // All [1..N] equivalent sets.
  const all = [
    // 0-equivalent sets.
    [nonAccepting, accepting]
      .filter(set => set.size > 0),
  ];


  let current;
  let previous;

  // Top of the stack is the current list of sets to analyze.
  current = all[all.length - 1];

  // Previous set (to check whether we need to stop).
  previous = all[all.length - 2];

  // Until we'll not have the same N and N-1 equivalent rows.
  while (!sameRow(current, previous)) {
    const newTransitionMap = {};

    for (const set of current) {
      // Handled states for this set.
      const handledStates = {};

      const [first, ...rest] = set;
      handledStates[first] = new Set([first]);

      // Have to compare each from the rest states with
      // the already handled states, and see if they are equivalent.
      restSets: for (const state of rest) {
        for (const handledState of Object.keys(handledStates)) {
          // This and some previously handled state are equivalent --
          // just append this state to the same set.
          if (areEquivalent(state, handledState)) {
            handledStates[handledState].add(state);
            handledStates[state] = handledStates[handledState];
            continue restSets;
          }
        }
        // Else, this state is not equivalent to any of the
        // handled states -- allocate a new set for it.
        handledStates[state] = new Set([state]);
      }

      // Add these handled states to all states map.
      Object.assign(newTransitionMap, handledStates);
    }

    // Update current transition map for the handled row.
    currentTransitionMap = newTransitionMap;

    let newSets = new Set(
      Object.keys(newTransitionMap)
        .map(state => newTransitionMap[state])
    );

    all.push([...newSets]);

    // Top of the stack is the current.
    current = all[all.length - 1];

    // Previous set.
    previous = all[all.length - 2];
  }

  // ---------------------------------------------------------------------------
  // Step 2: build minimized table from the equivalent sets.

  // Remap state numbers from sets to index-based.
  const remaped = new Map();
  let idx = 1;
  current.forEach(set => remaped.set(set, idx++));

  // Build the minimized table from the calculated equivalent sets.
  const minimized = {};

  for (const [set, idx] of remaped.entries()) {
    minimized[idx] = {};
    for (const symbol of alphabet) {
      // All states in a set are equivalent, so take the first one
      // to see where it goes on symbol.
      const originalState = [...set][0];

      const originalTransition = table[originalState][symbol];

      if (originalTransition) {
        minimized[idx][symbol] = remaped.get(
          currentTransitionMap[originalTransition]
        );
      }
    }
  }

  return minimized;
}

function sameRow(r1, r2) {
  if (!r2) {
    return false;
  }

  if (r1.length !== r2.length) {
    return false;
  }

  for (let i = 0; i < r1.length; i++) {
    const s1 = r1[i];
    const s2 = r2[i];

    if (s1.size !== s2.size) {
      return false;
    }

    if ([...s1].sort().join(',') !== [...s2].sort().join(',')) {
      return false;
    }
  }

  return true;
}

/**
 * Checks whether two states are N-equivalent, i.e. whether they go
 * to the same set on a symbol.
 */
function areEquivalent(s1, s2) {
  for (const symbol of alphabet) {
    if (!goToSameSet(s1, s2, symbol)) {
      return false;
    }
  }
  return true;
}

/**
 * Checks whether states go to the same set.
 */
function goToSameSet(s1, s2, symbol) {
  if (!currentTransitionMap[s1] || !currentTransitionMap[s2]) {
    return false;
  }
  return currentTransitionMap[s1][symbol] === currentTransitionMap[s2][symbol];
}

// -----------------------------------------------------------------------------
// Tests

// { '1': { a: 2, b: 3 }, '2': {}, '3': {} }
console.log('Original:', table);

// { '1': { a: 2, b: 2 }, '2': {} }
console.log('Minimized:', minimize(table));