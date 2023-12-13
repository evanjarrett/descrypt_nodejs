import {crypt} from "../crypt3.mjs";


console.log(crypt("test1234", "AA"));
console.log(crypt("test1234somethingreallylong", "AA"));


console.log(crypt("test1234", "AAlongersalt"));
console.log(crypt("test1234somethingreallylong2", "AAlongersalt"));


console.log(crypt("test1234", "DiffSalt"));
console.log(crypt("test1234somethinelsereallylongg", "DiffSalt"));