/*
 * Theorem Proving -- Propositional Calculus
 */

require("./types.js")(global);
let parser = require("./parser.js");

let database = [];

/*
 * Add facts to the knowledge base.
 */
function facts(...expressions) {
    for (let expr of expressions) {
        expr = toCNF(expr);
        collectConjunctions(database, expr);
    }

    return database;
}

function clear() {
    database = [];
}

function collectConjunctions(set, expr) {
    if (typeof expr === "string") set.push(expr);
    else if (expr.action !== AND) set.push(expr);
    else expr.args.map(collectConjunctions.bind(this, set)); // call recursively
}

function extractLiterals(expr) {
    let set = new Set();

    function helper(e) {
        if (typeof e === "string") set.add(e);
        else if (e.action === NOT) set.add(e.toString());
        else e.args.map(helper); // call recursively
    }

    helper(expr);
    return set;
}

/*
 * Try to prove a statement. Returns true or false depending on the validity of
 * the expression (according to the knowledge base).
 */
function prove(expression) { 
    // look at the union of the knowledge base and the negation of the expression,
    // and see if it is unsatisfiable (essentially proof by contradiction).
    let expr = new Expression(NOT, [expression]);

    let test = database.slice();
    collectConjunctions(test, toCNF(expr));

    let clauses = test.map(extractLiterals);

    while (true) {
        let newClauses = [];
        let n = clauses.length;
        // for every pair
        for (let i = 0; i < n; i++) {
            let A = clauses[i];

            inner:
            for (let j = i+1; j < n; j++) {
                let B = clauses[j];

                let result = resolve(A, B); 

                // contradiction!!!
                if (result.size === 0) return true;

                // check for tautology
                for (let lit of result) {
                    if (result.has(negate(lit))) // we have A OR NOT(A), so tautology
                        continue inner;
                }
                
                // whether we already have this statement
                let result_arr = Array.from(result);
                for (let clause of clauses.concat(newClauses)) {
                    let leftContain = result_arr.every(lit => clause.has(lit));
                    let rightContain = Array.from(clause).every(lit => result.has(lit));
                    if (leftContain && rightContain) continue inner;
                }

                newClauses.push(result);
            }
        }

        // we've tried everything; no proof
        if (newClauses.length === 0) return false;

        clauses = clauses.concat(newClauses);
    }
}

/* 
 * Negate a literal. Handles double negation.
 */
function negate(literal) {
    return literal.startsWith("¬") ? literal.slice(1) : "¬" + literal;
}

/*
 * Resolve a pair of expressions. A and B must be Sets of string literals.
 */
function resolve(A_list, B_list) {
    let A = Array.from(A_list);
    let B = Array.from(B_list);

    let unique_A = A.filter(literal => !B.includes(negate(literal)));
    let unique_B = B.filter(literal => !A.includes(negate(literal)));
    
    return new Set(unique_A.concat(unique_B));
}

/*
 * Converts an expression to Conjunctive Normal Form. Returns a copy.
 */
function toCNF(expression) {
    if (typeof expression === "string") return expression;

    return distributeOr(
           eliminateDoubleNegations(
           applyDeMorgan(
           replaceImplications(
           removeBiconditionals(
               expression.clone()
           )))));
}

function removeBiconditionals(expression) {
    if (typeof expression === "string") return expression;

    // replace biconditional with conjunction of implications
    if (expression.action === EQV) { 
        let AB = new Expression(IMPL, expression.args);
        let BA = new Expression(IMPL, [
            expression.args[1],
            expression.args[0]
        ]);
        expression = new Expression(AND, [AB, BA]);
    }

    expression.args = expression.args.map(removeBiconditionals);
    return expression;
}

function replaceImplications(expression) {
    if (typeof expression === "string") return expression;

    if (expression.action === IMPL) {
        let [A, B] = expression.args;

        expression = new Expression(OR, [
            new Expression(NOT, [A]),
            B
        ]);
    }

    expression.args = expression.args.map(replaceImplications);
    return expression;
}

function applyDeMorgan(expression) {
    if (typeof expression === "string") return expression;

    if (expression.action === NOT) {
        let arg = expression.args[0];
        if (typeof arg === "string") return expression;

        let [A, B] = arg.args;

        if (arg.action === AND) {
            expression = new Expression(OR, [
                new Expression(NOT, [A]),
                new Expression(NOT, [B])
            ]);
        } else if (arg.action === OR) {
            expression = new Expression(AND, [
                new Expression(NOT, [A]),
                new Expression(NOT, [B])
            ]);
        }
    }

    expression.args = expression.args.map(applyDeMorgan);
    return expression;
}

function eliminateDoubleNegations(expression) {
    if (typeof expression === "string") return expression;

    if (expression.action === NOT) {
        let arg = expression.args[0];

        if (arg.action === NOT)  {
            expression = arg.args[0];

            if (typeof expression === "string") return expression;
        }
    }

    expression.args = expression.args.map(eliminateDoubleNegations);
    return expression;
}

function distributeOr(expression) {
    if (typeof expression === "string") return expression;

    let [A, B] = expression.args;
    if (expression.action === OR) {
        if (typeof A === "string") {
            if (typeof B === "string") return expression; // A ∨ B

            if (B.action === AND) { // A ∨ (X ∧ Y) 
                let [X, Y] = B.args;

                expression = new Expression(AND, [
                    new Expression(OR, [A, X]),
                    new Expression(OR, [A, Y])
                ]);
            }
        } else if (A.action == AND) { // (X ∧ Y) ∨ B
            let [X, Y] = A.args;

            expression = new Expression(AND, [
                new Expression(OR, [X, B]),
                new Expression(OR, [Y, B])
            ]);
        }
    }

    expression.args = expression.args.map(distributeOr);
    return expression;
}


module.exports = {
    facts,
    clear,
    prove,
    Expression,
    parse: parser.parse,
};
