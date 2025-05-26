import * as assert from "assert";
import { L5programTypeof, L5typeof } from "./src/L5/L5-typecheck";

// Helper function to unwrap the Result from L5typeof
function getTypeofValue(exp: string): string | Error {
    const result = L5typeof(exp);
    if (result.tag === 'Ok') {
        return result.value;
    } else {
        // Convert Failure to Error
        return new Error(result.message);
    }
}

function getTypeofProgram(exp: string): string | Error {
    const result = L5programTypeof(exp);
    if (result.tag === 'Ok') {
        return result.value;
    } else {
        // Convert Failure to Error
        return new Error(result.message);
    }
}

describe("L5 Type Checker", () => {
    describe("Type Definition Tests", () => {
        it("should correctly type a boolean definition", () => {
            assert.deepEqual(getTypeofValue("(define (x : boolean) (if (> 1 2) #t #f))"), "void");
        });

        it("should correctly type a number definition", () => {
            assert.deepEqual(getTypeofValue("(define (x : number) 5)"), "void");
        });

        it("should correctly type a function definition with number -> number type", () => {
            assert.deepEqual(getTypeofValue("(define (x : (number -> number)) (lambda ((x : number)) : number (+ 1 x)))"), "void");
        });

        it("should correctly type a polymorphic identity function", () => {
            assert.deepEqual(getTypeofValue("(define (x : (T -> T)) (lambda ((x : T)) : T x))"), "void");
        });

        it("should correctly type a binary function definition", () => {
            assert.deepEqual(getTypeofValue("(define (foo : (number * number -> number)) (lambda((x : number) (y : number)) : number (+ x y)))"), "void");
        });

        it("should correctly type a nullary function definition", () => {
            assert.deepEqual(getTypeofValue("(define (x : (Empty -> number)) (lambda () : number 1))"), "void");
        });
    });

    describe("Type Error Tests", () => {
        it("should detect type mismatch between number and boolean", () => {
            assert.deepEqual(getTypeofValue("(define (x : number) #t)") instanceof Error, true);
        });

        it("should detect type mismatch between boolean and number", () => {
            assert.deepEqual(getTypeofValue("(define (x : boolean) 5)") instanceof Error, true);
        });

        it("should detect return type mismatch in function", () => {
            assert.deepEqual(getTypeofValue("(define (x : (number -> boolean)) (lambda ((x : number)) : number (+ 1 x)))") instanceof Error, true);
        });

        it("should detect parameter count mismatch in function", () => {
            assert.deepEqual(getTypeofValue("(define (x : (number -> number)) (lambda () : number 1))") instanceof Error, true);
        });

        it("should detect binding type mismatch in let expression", () => {
            assert.deepEqual(getTypeofValue("(define (x : number) (let (((y : number) #t)) y))") instanceof Error, true);
        });

        it("should detect body type mismatch with return type", () => {
            assert.deepEqual(getTypeofValue("(define (x : boolean) (let (((y : number) 5)) y))") instanceof Error, true);
        });

        it("should detect type error in operator arguments", () => {
            assert.deepEqual(getTypeofValue("(define (x : number) (let (((y : boolean) #t)) (+ y 1)))") instanceof Error, true);
        });
    });

    describe("Program Type Tests", () => {
        it("should correctly type a simple program with number", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : number) 5) (+ x 1))"), "number");
        });

        it("should correctly type a simple program with boolean", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : boolean) #t) x)"), "boolean");
        });

        it("should correctly type a program with function application", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : (Empty -> number)) (lambda () : number 1)) (x))"), "number");
        });

        it("should correctly type a program with multiple definitions", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : number) 5) (define (y : number) 6) (+ x y))"), "number");
        });

        it("should correctly type a program with function definition and application", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : (number -> number)) (lambda ((n : number)) : number (+ n 1))) (x 5))"), "number");
        });

        it("should correctly type a program with let expression", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (x : number) (let (((y : number) 5)) (- 0 y))) (+ 7 x))"), "number");
        });
    });

    describe("Pair Type Tests", () => {
        it("should correctly type a pair of number and boolean", () => {
            assert.deepEqual(getTypeofValue("(define (p : (Pair number boolean)) (cons 5 #t))"), "void");
        });

        it("should correctly type car of a pair", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (p : (Pair number boolean)) (cons 5 #t)) (car p))"), "number");
        });

        it("should correctly type cdr of a pair", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (p : (Pair number boolean)) (cons 5 #t)) (cdr p))"), "boolean");
        });

        it("should correctly type a pair with function and boolean", () => {
            assert.deepEqual(getTypeofValue("(define (p : (Pair (number -> number) boolean)) (cons (lambda ((x : number)) : number (* x 2)) #t))"), "void");
        });

        it("should correctly type a nested pair", () => {
            assert.deepEqual(getTypeofValue("(define (p : (Pair number (Pair string boolean))) (cons 5 (cons \"hello\" #t)))"), "void");
        });

        it("should correctly type element access in nested pair", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (p : (Pair number (Pair string boolean))) (cons 5 (cons \"hello\" #t))) (car (cdr p)))"), "string");
        });

        it("should correctly type a polymorphic pair swap function", () => {
            assert.deepEqual(getTypeofValue("(define (swap : ((Pair T1 T2) -> (Pair T2 T1))) (lambda ((p : (Pair T1 T2))) : (Pair T2 T1) (cons (cdr p) (car p))))"), "void");
        });

        it("should detect pair element type mismatch", () => {
            assert.deepEqual(getTypeofValue("(define (p : (Pair number boolean)) (cons #t 5))") instanceof Error, true);
        });

        it("should detect type error when using cdr result incorrectly", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (p : (Pair number boolean)) (cons 5 #t)) (+ (cdr p) 1))") instanceof Error, true);
        });

        it("should detect type error when using car result incorrectly", () => {
            assert.deepEqual(getTypeofProgram("(L5 (define (p : (Pair number boolean)) (cons 5 #t)) (if (car p) #t #f))") instanceof Error, true);
        });
    });

    describe("Quote Expression Tests", () => {

        it("should correctly type a quoted pair of numbers", () => {
            assert.deepEqual(getTypeofProgram("(L5 (quote (4 . 7)))"), "(Pair number number)");
        });


        it("should correctly type a quoted expression with shorthand notation", () => {
            assert.deepEqual(getTypeofProgram("(L5 '(4 . 7))"), "(Pair number number)");
        });

        it("should correctly type a quoted literal with shorthand notation", () => {
            assert.deepEqual(getTypeofProgram("(L5 '5)"), "literal");
        });

        it("should correctly type a quoted boolean and boolean with shorthand notation", () => {
            assert.deepEqual(getTypeofProgram("(L5 '(#t . #f))"), "(Pair boolean boolean)");
        });

        it("should correctly type a quoted boolean adn nmber with shorthand notation", () => {
            assert.deepEqual(getTypeofProgram("(L5 '(#t . 10))"), "(Pair boolean number)");
        });

        it("should correctly type a quoted number and literal with shorthand notation", () => {
            assert.deepEqual(getTypeofProgram("(L5 '(4 . 'abc))"), "(Pair number literal)");
        });




    });
});