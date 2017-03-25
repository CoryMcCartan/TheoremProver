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
