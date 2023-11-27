This is the Coq development with the SETTA 2023 paper: *Formalization of Lambda Calculus With Explicit Names as a Nominal Reasoning Framework.*



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