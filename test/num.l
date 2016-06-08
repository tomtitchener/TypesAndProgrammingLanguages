# Church numerals
#
# Bindings
#
tru   = (λt.λf.t);
fls   = (λt.λf.f);
zero  = (λs.λz.z);
one   = (λs.λz.s z);
two   = (λs.λz.s (s z));
three = (λs.λz.s (s (s z)));
four  = (λs.λz.s (s (s (s z))));
five  = (λs.λz.s (s (s (s (s z)))));
six   = (λs.λz.s (s (s (s (s (s z))))));
nine  = (λs.λz.s (s (s (s (s (s (s (s (s z)))))))));
scc   = (λn.λs.λz.s (n s z));
scc'  = (λn.λs.λz.n s (s z));
plus  = (λm.λn.λs.λz. m s (n s z));
times = (λm.λn.λs. m (n s));
pair  = (λf.λs.λb. b f s);
#
and   = (λb.λc. b c fls);
exp   = (λm.λn.n (times m) one);
iszro = (λm.m (λx. fls) tru);
fst   = (λp. p tru);
snd   = (λp. p fls);
zz    = (pair zero zero);
ss    = (λp. pair (snd p) (plus one (snd p)));
prd   = (λm.fst (m ss zz));
sub   = (λm.λn.n prd m);
equal = (λm.λn.and (iszro (sub m n)) (iszro (sub n m)));
#
# Statements
#
(scc zero);
(scc' zero);
(plus zero zero);
(plus zero one);
(plus one one);
(plus one two);
(plus two two);
(times two two);
(times zero zero);
(times zero four);
(times one one);
(times one two);
(exp two two);
(exp one two);
(exp one one);
(exp three two);
(iszro one);
(iszro zero);
#
(prd zero);
(prd one);
(prd two);
(prd three);
(sub two one);
(sub three one);
(sub nine six);
(equal one one);
(equal zero one);
(equal zero zero);
(equal nine nine);
(equal nine zero);
