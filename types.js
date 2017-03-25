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
