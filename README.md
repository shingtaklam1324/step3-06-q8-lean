# 2006 STEP 3 Question 8

This is a formalisation in Lean of the solution to Question 8 on the 2006 STEP 3 paper, which can be found [here](https://stepdatabase.maths.org/database/db/06/06-S3.pdf).

[step3.lean](src/step3.lean) is the solution which just uses the rules given in the question.

[polynomial_derivations.lean](src/polynomial_derivations.lean) builds up polynomial derivations, proving the structure theorem and also establishing an equivalence between polynomials and polynomial derivations.

[step_3_derivations.lean](src/step3_derivations.lean) is the solution to the problem which uses the polynomial derivations built up in the previous file.

Thanks to [Kevin Buzzard](https://github.com/kbuzzard/) for helping me do this.