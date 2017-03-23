let chai = require("chai").should();

describe("stuff", function() {
   it("should perform basic arithmetic", function() {
       var test = 5 + 2;
       test.should.equal(7);
   });
});
