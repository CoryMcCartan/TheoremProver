/*
 * Theorem Proving -- Propositional Calculus
 */

const NOT = Symbol("negation");
const AND = Symbol("conjunction");
const OR = Symbol("disjunction");
const IMPL = Symbol("implication");
const EQV = Symbol("equivalence");

let database = [];

/*
 * Add facts to the knowledge base.
 */
function facts(...expressions) {
    for (expr of expressions) {
        expr = toCNF(expr);
        collectConjunctions(database, expr);
    }
}

function collectConjunctions(set, expr) {
    if (typeof expr === "string") set.push(expr);
    else if (expr.action !== AND) set.push(expr);
    else expr.args.map(collectConjunctions.bind(this, set)); // call recursively
}

/*
 * Try to prove a statement. Returns true or false depending on the validity of
 * the expression (according to the knowledge base).
 */
function prove(expression) {
    // look at the union of the knowledge base and the negation of the expression,
    // and see if it is unsatisfiable (essentially proof by contradiction).
    let expr = new Expression(NOT, [expression]);
    if (database.includes(expr)) return true;

    let test = database.slice();
    collectConjunctions(test, toCNF(expr));

    while (true) {
        let newClauses = [];
        let n = test.length;
        let strings = test.map(x => x.toString());
        // for every pair
        for (let i = 0; i < n; i++) {
            let A = test[i];

            for (let j = i+1; j < n; j++) {
                let B = test[j];

                let result = resolve(A, B); 

                // contradiction!!!
                if (result === undefined) return true;

                // already have this, not useful
                if (strings.includes(result.toString())) continue;

                newClauses.push(result);
            }
        }

        exhausted = newClauses.map(x => x.toString()).every(s => strings.includes(s));
        // we've tried everything; no proof
        if (exhausted) return false;

        test = test.concat(newClauses);
    }
}

/*
 * Resolve a pair of expressions, each of which must be a disjunction of literals.
 */
function resolve(A, B) {
    // collect all disjunctions
    let A_vars = new Set();
    let B_vars = new Set();
    let collectLiterals = function(set, expr) {
        if (typeof expr === "string") set.add(expr);
        else if (expr.action === NOT) set.add(expr.toString());
        else if (expr.action === AND) throw new Error("No conjunctions allowed in application of resolution.");
        else expr.args.map( collectLiterals.bind(this, set) ); // call recursively
    }
    collectLiterals(A_vars, A);
    collectLiterals(B_vars, B);

    // determine which can be eliminated and which cannot
    let unique = new Set();
    for (let literal of A_vars) {
        // negate literal (and handle double negatives)
        let negation = literal.startsWith("¬") ? literal.slice(1) : "¬" + literal;
        let found = false;

        for (let other of B_vars) {
            if (other === negation) {
                // eliminate
                A_vars.delete(literal);
                B_vars.delete(other);

                found = true;
                break;
            }
        } 

        if (!found)
            unique.add(literal);
    }
    // add in unique B literals
    for (let literal of B_vars) {
        let found = false;

        for (let other of A_vars) {
            if (other === literal) {
                found = true;
                break;
            }
        } 

        if (!found)
            unique.add(literal);
    }

    // create new disjunction
    unique = Array.from(unique);
    let result = unique.pop();
    while (unique.length) {
        result = new Expression(OR, [unique.pop(), result]);
    }

    return result;
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
           removeBijections(
               expression.clone()
           )))));
}

function removeBijections(expression) {
    if (typeof expression === "string") return expression;

    // replace bijection with conjunction of implications
    if (expression.action === EQV) { 
        AB = new Expression(IMPL, expression.args);
        BA = new Expression(IMPL, [
            expression.args[1],
            expression.args[0]
        ]);
        expression = new Expression(AND, [AB, BA]);
    }

    expression.args = expression.args.map(removeBijections);
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


/*
 * A logic expression.  One of five types: negation, conjunction, disjunction,
 * implication, or equivalence.
 */
class Expression {
    /*
     * Create an expression. Passed an action (Symbol) and an array of
     * arguments, each of which must be an expression or a string. All actions
     * except negation require two arguments; negation allows only one.
     */
    constructor(action, args) {
        if (!action || typeof action !== "symbol")
            throw new Error("Need string action.")
        if (!args || !(args instanceof Array))
            throw new Error("Need array of arguments.");
        if (action === NOT && args.length !== 1)
            throw new Error(`Expected one argument for negation, but got ${args}`);
        else if (action !== NOT && args.length !== 2)
            throw new Error(`Expected two arguments, but got ${args}`);

        for (let arg of args)
            if (!(arg instanceof Expression || typeof arg === "string"))
                throw new Error("Arguments must be strings or Expressions.");

        this.action = action;
        this.args = args;
    }

    toString() {
        if (this.action === NOT)
            return `¬${this.args[0].toString()}`;
        else
            return `(${this.args[0].toString()} ${translate(this.action)} ${this.args[1].toString()})`;
    }
    
    clone() {
        let [A, B] = this.args;
        if (typeof A !== "string") A = A.clone();
        if (this.action !== NOT && typeof B !== "string") B = B.clone();

        if (this.action === NOT)
            return new Expression(NOT, [A]);
        else
            return new Expression(this.action, [A, B]);
    }
}

/*
 * Translate a operator enum (Symbol) to a string character.
 */
function translate(key) {
    return {
       [NOT]: "¬", 
       [AND]: "∧", 
       [OR]: "∨", 
       [IMPL]: "→", 
       [EQV]: "↔", 
    }[key] || new Error(`No matching symbol or action found: "${key}"`);
}

/*
 * Parse a string into an Expression object. 
 */
function parse(str) {
    const OP = Symbol("Operator"), 
        PAREN = Symbol("Parenthesis"), 
        VAR = Symbol("Variable");

    // tokenize
    let tokens = [];
    let current = {};
    for (let ch of str) {
        if (" \n\t".includes(ch)) continue; // whitespace

        let type;
        if (/[∧∨¬!→↔&|<>-]/.test(ch)) type = OP
        else if (/[()]/.test(ch)) type = PAREN
        else type = VAR;

        if (type === current.type && type != PAREN) {
            current.value += ch;    
        } else { // tack on last token, start new one
            current = {
                type,
                value: ch,
            };
            tokens.push(current);
        }
    }

    // parse, using shunting-yard algorithm
    let output = [];
    let operators = [];

    // returns precedence of given operator
    let precedence = function(token) {
       if (["->", "<->", "→", "↔"].includes(token.value)) return 0; 
       else if (["∧", "∨", "&", "|"].includes(token.value)) return 1;
       else if (["¬", "!"].includes(token.value)) return 2;

       else throw new Error(`Unrecognized operator ${token.value}`);
    };
    // outputs operator by appling it to top two elements of output stack
    let out = function(operator) {
        let expression;
        let v = operator.value;

        if (v === "¬" || v === "!") { // negation
            expression = new Expression(NOT, [output.pop()]);
        } else {
            let type;
            if (v === "->" || v === "→") type = IMPL;
            else if (v === "<->" || v === "↔") type = EQV;
            else if (v === "∧" || v === "&") type = AND;
            else if (v === "∨" || v === "|") type = OR;

            right = output.pop();
            left = output.pop();
            expression = new Expression(type, [left, right]);
        }

        output.push(expression);
    };

    for (let t of tokens) {
        if (t.type === OP) {
            while (true) {
                let last = operators[operators.length - 1];
                if (last === undefined) break;
                if (last.type === PAREN) break;
                if (precedence(t) >= precedence(last)) break;

                out(operators.pop());
            }

            operators.push(t);
        }
        if (t.type === VAR) output.push(t.value);
        if (t.value === "(") operators.push(t);
        if (t.value === ")") {
            while (true) {
                let op = operators.pop();
                if (op === undefined) 
                    throw new Error("Mismatched parenthesis.");
                if (op.value === "(") break;

                out(op);
            }
        }
    }

    while (true) {
        let op = operators.pop();
        if (op === undefined) break;
        if (op.value === "(" || op.value === ")") 
            throw new Error("Mismatched parenthesis.");

        out(op);
    }

    return output[0];
}

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
