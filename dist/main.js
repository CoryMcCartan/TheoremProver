(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.theorem = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
(function (global){
require("./types.js")(global);

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
            else throw new Error(`Unrecognized operator: "${v}"`);

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

module.exports = {
    parse,
};

}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{"./types.js":3}],2:[function(require,module,exports){
(function (global){
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
           removeBijections(
               expression.clone()
           )))));
}

function removeBijections(expression) {
    if (typeof expression === "string") return expression;

    // replace bijection with conjunction of implications
    if (expression.action === EQV) { 
        let AB = new Expression(IMPL, expression.args);
        let BA = new Expression(IMPL, [
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


module.exports = {
    facts,
    clear,
    prove,
    Expression,
    parse: parser.parse,
};

}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{"./parser.js":1,"./types.js":3}],3:[function(require,module,exports){
const NOT = Symbol("negation");
const AND = Symbol("conjunction");
const OR = Symbol("disjunction");
const IMPL = Symbol("implication");
const EQV = Symbol("equivalence");


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
            throw new TypeError("Need action constant.")
        if (!args || !(args instanceof Array))
            throw new Error("Need array of arguments.");
        if (action === NOT && args.length !== 1)
            throw new Error(`Expected one argument for negation, but got ${args}`);
        else if (action !== NOT && args.length !== 2)
            throw new Error(`Expected two arguments, but got ${args}`);

        for (let arg of args)
            if (!(arg instanceof Expression || typeof arg === "string"))
                throw new TypeError("Arguments must be strings or Expressions.");

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
    let dict = {
        [NOT]: "¬", 
        [AND]: "∧", 
        [OR]: "∨", 
        [IMPL]: "→", 
        [EQV]: "↔", 
    };

    if (dict[key] === undefined)
        throw new Error("No matching symbol or action found.");
    else
        return dict[key];
}

module.exports = function(obj) {
    obj.NOT = NOT;
    obj.AND = AND;
    obj.OR = OR;
    obj.IMPL = IMPL
    obj.EQV = EQV;
    obj.Expression = Expression;
};

},{}]},{},[2])(2)
});