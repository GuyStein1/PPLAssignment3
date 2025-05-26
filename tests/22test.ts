import { parseL5 } from "../src/L5/L5-ast"; // adjust path as needed
import { typeofProgram } from "../src/L5/L5-typecheck";
import { makeEmptyTEnv } from "../src/L5/TEnv";
import { unparseTExp } from "../src/L5/TExp";

const test = (code: string) => {
    const parsed = parseL5(code);  // not parseL5Exp
    if (parsed.tag === "Failure") {
        console.log("Parse error:", parsed.message);
    } else {
        const result = typeofProgram(parsed.value, makeEmptyTEnv());
        console.log("Type:", result.tag === "Ok" ? `Ok: ${unparseTExp(result.value)}` : `Error: ${result.message}`);
    }
};

test(`(L5
  (define (id : [number -> number]) (lambda (x) x))
  (id 5))`);
