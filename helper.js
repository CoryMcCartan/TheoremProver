require("./types.js")(global);

/*
 * Tests whether two statements are logically equivalent by contstructing their 
 * truth table.
 */
function eq(A, B) {
    // collect all variables to generate combinations of elements
    let vars = new Set();
    let collectElements = function(expr) {
        if (typeof expr === "string") vars.add(expr);
        else expr.args.map(collectElements);
    }
    collectElements(A);
    collectElements(B);

    // evaluate an expression
    let evaluate = function(expr, values) {
        if (typeof expr === "string") return values[expr];

        let [A, B] = expr.args;
        let eA = evaluate(A, values);
        let eB = B === undefined ? 0 : evaluate(B, values); // b might not exist

        if (expr.action === NOT) return !eA;
        if (expr.action === AND) return eA && eB;
        if (expr.action === OR) return eA || eB;
        if (expr.action === IMPL) return !eA || eB;
        if (expr.action === EQV) return (!eA || eB) && (!eB || eA);
    };

    varnames = Array.from(vars);
    for (combination of enumerateAll(varnames)) {
        let A_result = evaluate(A, combination);
        let B_result = evaluate(B, combination);

        if (A_result !== B_result) return false;
    }

    // statements are equivalent for all possible combinations of values
    return true; 
}

/*
 * Generator that enumerates all binary possibilities of a set of up to 15 variables.
 */
function * enumerateAll(vars) {
    let n = vars.length;

    for (let i = 0; i < (1 << n); i++) {
        let obj = {};

        for (let j = 0; j < n; j++) {
            let value = (i & (1 << j)) > 0; // bitmask, returns true if variable should be true
            obj[vars[j]] = value;
        }

        yield obj;
    }
}

module.exports = { 
    eq,
};
