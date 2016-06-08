# recursion
#
# Bindings
#
omega = ((λx.x x) (λx.x x));
fix   = (λf.(λx.f (λy. x x y)) (λx.f (λy. x x y)));
tru   = (λt.λf.t);
fls   = (λt.λf.f);
test  = (λl.λm.λn. l m n);
plus  = (λm.λn.λs.λz. m s (n s z));
zero  = (λs.λz.z);
one   = (λs.λz.s z);
pair  = (λf.λs.λb. b f s);
times = (λm.λn.λs. m (n s));
#
iszro = (λm.m (λx. fls) tru);
fst   = (λp. p tru);
snd   = (λp. p fls);
zz    = (pair zero zero);
ss    = (λp. pair (snd p) (plus one (snd p)));
prd   = (λm.fst (m ss zz));
factg = (λf.λn.test (iszro n) one (times n (f (prd n))));
fact  = (fix factg);
four  = (λs.λz.s (s (s (s z))));
twentyfour = (λs.λz.(s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))));
#
# Statements
#
(omega);
(fact four);
