let chai = require("chai").should();
let thm = require("../theorem.js");
let parser = require("../parser.js");
require("../types.js")(global);

describe("Expression", function() {
    describe("constructor()", function() {
        it("should create an Expression object from literals.", function() {
            let e = new Expression(AND, ["A", "B"]);

            (e.action === AND).should.be.true;
            e.args.should.have.length(2);
        });
        it("should create negations with only one argument.", function() {
            let e = new Expression(NOT, ["A"]);

            (e.action === NOT).should.be.true;
            e.args.should.have.length(1);
        });
        it("should create an Expression object from expressions.", function() {
            let a = new Expression(NOT, ["A"])
            let b = new Expression(NOT, ["B"])
            let e = new Expression(AND, [a, b]);

            (e.action === AND).should.be.true;
            e.args.should.have.length(2);
        });
        it("should only accept the proper number of arguments.", function() {
            let test_or_1 = () => new Expression(OR, ["A", "B", "C"]);
            let test_or_2 = () => new Expression(OR, ["A"]);
            let test_not = () => new Expression(NOT, ["A", "B"]);
            let test_none = () => new Expression(OR);

            test_or_1.should.throw("Expected two arguments");
            test_or_2.should.throw("Expected two arguments");
            test_not.should.throw("Expected one argument for negation");
            test_none.should.throw("Need array of arguments");
        });
        it("should accept only proper types for arguments.", function() {
            let e1 = () => new Expression(OR, [57.7, 88]);
            let e2 = () => new Expression(88, ["A"]);

            e1.should.throw(TypeError);
            e2.should.throw(TypeError);
        })
    });
    describe("toString()", function() {
        it("should properly handle NOT expressions.", function() {
            let e = new Expression(NOT, ["A"]);

            e.toString().should.equal("¬A");
        });
        it("should properly handle other expressions.", function() {
            let e = new Expression(IMPL, ["A", "B"]);

            e.toString().should.equal("(A → B)");
        });
        it("should properly handle compound expressions.", function() {
            let a = new Expression(NOT, ["A"])
            let b = new Expression(NOT, ["B"])
            let e = new Expression(IMPL, [a, b]);

            e.toString().should.equal("(¬A → ¬B)");
        });
        it("should not translate an invalid expression action.", function() {
            let e = new Expression(Symbol(), ["A", "B"]);
            let f = () => e.toString();
            f.should.throw("No matching symbol");
        });
    });
    describe("clone()", function() {
        it("should clone the expression and detach the reference.", function() {
            let e = new Expression(IMPL, ["A", "B"]);
            let e_clone = e.clone();
            // check equality
            (e_clone.action === IMPL).should.be.true;
            e.args[0].should.equal("A");
            e.args[1].should.equal("B");
            // check references
            e = ["RANDOM"];
            e.should.not.equal(e_clone);
        });
        it("should clone compound expressions.", function() {
            let a = new Expression(NOT, ["A"])
            let b = new Expression(NOT, ["B"])
            let e = new Expression(IMPL, [a, b]);
            let e_clone = e.clone();
            // check equality
            (e_clone.action === IMPL).should.be.true;
            e_clone.args[0].should.not.equal(a);
            e_clone.args[1].should.not.equal(b);
        });
    });
});
describe("parse()", function() {
    let simpleTests = [
        {str: "A→B", action: IMPL, a: "A", b: "B"},
        {str: "A->B", action: IMPL, a: "A", b: "B"},
        {str: "A<->B", action: EQV, a: "A", b: "B"},
        {str: "A↔B", action: EQV, a: "A", b: "B"},
        {str: "A&B", action: AND, a: "A", b: "B"},
        {str: "A∧B", action: AND, a: "A", b: "B"},
        {str: "A|B", action: OR, a: "A", b: "B"},
        {str: "A∨B", action: OR, a: "A", b: "B"},
        {str: "!A", action: NOT, a: "A", b: undefined},
        {str: "¬A", action: NOT, a: "A", b: undefined},
    ];

    simpleTests.forEach(function(test) {
        it(`should parse "${test.str}" correctly.`, function() {
            let e = parser.parse(test.str);

            (e.action === test.action).should.be.true;
            (e.args[0] === test.a).should.be.true;
            (e.args[1] === test.b).should.be.true;
        });
    });
    it("should ignore whitespace.", function() {
        let e = parser.parse(` A\n &\tB`);
        (e.action === AND).should.be.true;
        e.args[0].should.equal("A");
        e.args[1].should.equal("B");
    });
    it("should parse compound expressions correctly.", function() {
        let e = parser.parse("(A&B)->(B|C)");
        (e.action === IMPL).should.be.true;

        let [L, R] = e.args;
        (L.action === AND).should.be.true;
        L.args[0].should.equal("A");
        L.args[1].should.equal("B");
        (R.action === OR).should.be.true;
        R.args[0].should.equal("B");
        R.args[1].should.equal("C");
    });
    it("should handle precedence correctly.", function() {
        let e = parser.parse("!A->B|C");
        (e.action === IMPL).should.be.true;

        let [L, R] = e.args;
        (L.action === NOT).should.be.true;
        L.args[0].should.equal("A");
        (L.args[1] === undefined).should.be.true;
        (R.action === OR).should.be.true;
        R.args[0].should.equal("B");
        R.args[1].should.equal("C");
    });
    it("should catch unmatched parentheses.", function() {
        let e = () => parser.parse("(A & B");
        e.should.throw("Mismatched parenthesis");

        let f = () => parser.parse("(A|C & B))");
        f.should.throw("Mismatched parenthesis");
    });
    it("should only allow for valid operators.", function() {
        let e = () => parser.parse("A ->>> B");
        e.should.throw("Unrecognized operator");

        let f = () => parser.parse("A&B|C ->>> D");
        f.should.throw("Unrecognized operator");
    });
});
describe("facts()", function() {
    beforeEach(thm.clear);

    it("should take facts and collect them in a database", function() {
        let e = parser.parse("A->B");

        let db = thm.facts(e);

        // check expression matches NOT A OR B
        let expr = db[0];
        (expr.action === OR).should.be.true;
        (expr.args[0].action === NOT).should.be.true;
        expr.args[0].args[0].should.equal("A");
        expr.args[1].should.equal("B");
    });
    it("should break up conjunctions", function() {
        let f = parser.parse("C&D");

        let db = thm.facts(f);

        db.should.contain("C");
        db.should.contain("D");
    }); 
    it("should properly handle double implications", function() {
        let e = parser.parse("A<->B");

        let db = thm.facts(e);

        // check expression matches NOT A OR B
        let expr = db[0];
        (expr.action === OR).should.be.true;
        (expr.args[0].action === NOT).should.be.true;
        expr.args[0].args[0].should.equal("A");
        expr.args[1].should.equal("B");

        expr = db[1];
        (expr.action === OR).should.be.true;
        (expr.args[0].action === NOT).should.be.true;
        expr.args[0].args[0].should.equal("B");
        expr.args[1].should.equal("A");
    });
    it("should handle multiple arguments", function() {
        let db = thm.facts("A", "B");

        db[0].should.equal("A");
        db[1].should.equal("B");
    });
});
describe("prove()", function() {
    this.timeout(500);
    beforeEach(thm.clear);

    let proofs = [
        {from: ["A"], prove: "A", result: true},
        {from: ["A→B", "A"], prove: "B", result: true},
        {from: ["!(!A)"], prove: "A", result: true},
        {from: ["A|B&C"], prove: "A|B&C", result: true},
        {from: ["A|B&C->D|(!E)", "A&C", "!D"], prove: "!E", result: true},
        {from: ["A→B", "B->C"], prove: "A->B", result: true},
        {from: [], prove: "A", result: false},
        {from: ["A→B"], prove: "C", result: false},
        {from: ["A|(!A)"], prove: "B", result: false},
    ];

    proofs.forEach(function(test) {
        it(`should ${test.result ? "" : "not "}prove "${test.prove}" ` +
           `from "${test.from.join(" ∧ ")}."`, function() {
            let stmts = test.from.map(thm.parse);
            let db = thm.facts(...stmts);

            let query = thm.parse(test.prove);
            let result = thm.prove(query);

            result.should.equal(test.result);
        });
    });
});
