This is the Coq development with the SETTA 2023 paper: *Formalization of Lambda Calculus With Explicit Names as a Nominal Reasoning Framework.*

### Publication
Wan, X., Cao, Q. (2024). Formalization of Lambda Calculus with Explicit Names as a Nominal Reasoning Framework. In: Hermanns, H., Sun, J., Bu, L. (eds) Dependable Software Engineering. Theories, Tools, and Applications. SETTA 2023. Lecture Notes in Computer Science, vol 14464. Springer, Singapore. https://doi.org/10.1007/978-981-99-8664-4_15

For the paper, we refer readers to https://link.springer.com/chapter/10.1007/978-981-99-8664-4_15

#### **How to build**
Tested on Coq 8.15.2.

```
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

#### Files (Details Updated Later)

The formalization of lambda calculus, alpha-equivalence and the Church-Rosser theorem can be found in <u>*lambda_binding.v.*</u>

Its application to let-binding in FOL can be found in the <u>*Demo*</u> folder.

#### Correspondence with paper

For historical development reasons, the type of lambda terms are called *tm* in lambda_binding.v, while it is called *term* in the paper.
