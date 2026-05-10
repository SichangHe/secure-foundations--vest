use alloc::vec::Vec;

use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that repeats [C] combinator [self.1] times.
pub struct RepeatN<C>(pub C, pub usize);

impl<C: View> View for RepeatN<C> {
    type V = RepeatN<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        RepeatN(self.0@, self.1)
    }
}

impl<C: SecureSpecCombinator> RepeatN<C> {
    /// Helper function for parsing [n] instances of [C] from [s].
    pub closed spec fn spec_parse_helper(&self, s: Seq<u8>, n: usize) -> Option<(int, Seq<C::Type>)>
        decreases n,
    {
        if n == 0 {
            Some((0, seq![]))
        } else {
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Some((m, vs)) => match self.0.spec_parse(s.skip(m as int)) {
                    Some((k, v)) => Some((m + k, vs.push(v))),
                    None => None,
                },
                None => None,
            }
        }
    }

    proof fn lemma_spec_parse_err_unrecoverable(&self, s: Seq<u8>, n1: usize, n2: usize)
        ensures
            n1 <= n2 ==> self.spec_parse_helper(s, n1) is None ==> self.spec_parse_helper(
                s,
                n2,
            ) is None,
        decreases n2,
    {
        if n1 <= n2 && self.spec_parse_helper(s, n1) is None {
            if n2 > 0 && n1 < n2 {
                self.lemma_spec_parse_err_unrecoverable(s, n1, (n2 - 1) as usize);
            }
        }
    }
}

impl<C: SecureSpecCombinator> RepeatN<C> {
    spec fn wf_helper(&self, vs: Seq<C::Type>, n: usize) -> bool {
        &&& vs.len() == n
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }

    proof fn theorem_serialize_parse_roundtrip_helper(&self, vs: Seq<C::Type>, n: usize)
        requires
            self.requires(),
        ensures
            self.wf_helper(vs, n) ==> self.spec_parse_helper(self.spec_serialize(vs), n) == Some(
                (self.spec_serialize(vs).len() as int, vs),
            ),
        decreases vs.len(), n,
    {
        if self.wf_helper(vs, n) && n > 0 {
            let vs_prev = vs.drop_last();
            let v = vs.last();
            let suf = self.0.spec_serialize(v);

            // spec_serialize(vs) = spec_serialize(vs_prev) + suf
            assert(self.spec_serialize(vs) == self.spec_serialize(vs_prev) + suf) by {
                assert(vs.drop_last() == vs_prev);
                assert(vs.last() == v);
            };

            let pre = self.spec_serialize(vs_prev);
            assert(self.wf_helper(vs_prev, (n - 1) as usize));

            // IH: spec_parse_helper(pre, n-1) = Some((pre.len(), vs_prev))
            self.theorem_serialize_parse_roundtrip_helper(vs_prev, (n - 1) as usize);
            assert(self.spec_parse_helper(pre, (n - 1) as usize) is Some);

            // prefix_secure: spec_parse_helper(pre + suf, n-1) = spec_parse_helper(pre, n-1)
            self.lemma_prefix_secure_helper(pre, suf, (n - 1) as usize);

            // self.0.theorem_serialize_parse_roundtrip(v): self.0.spec_parse(suf) = Some((suf.len(), v))
            self.0.theorem_serialize_parse_roundtrip(v);

            // spec_serialize(vs).skip(pre.len()) = suf
            let m = pre.len() as int;
            assert((pre + suf).skip(m) =~= suf);

            // vs = vs_prev.push(v)
            assert(vs == vs_prev.push(v));
            assert(pre.len() + suf.len() == (pre + suf).len());
        }
    }

    proof fn theorem_parse_serialize_roundtrip_helper(&self, buf: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(buf, n) matches Some((m, vs)) ==> {
                &&& self.wf_helper(vs, n)
                &&& self.spec_serialize(vs) == buf.take(m)
            },
        decreases n,
    {
        if n > 0 {
            self.theorem_parse_serialize_roundtrip_helper(buf, (n - 1) as usize);
            if let Some((m_prev, vs_prev)) = self.spec_parse_helper(buf, (n - 1) as usize) {
                self.0.theorem_parse_serialize_roundtrip(buf.skip(m_prev as int));
                if let Some((k, v)) = self.0.spec_parse(buf.skip(m_prev as int)) {
                    // spec_parse_helper(buf, n) = Some((m_prev + k, vs_prev.push(v)))
                    // spec_serialize(vs_prev.push(v)) = spec_serialize(vs_prev) + inner.spec_serialize(v)
                    //   = buf.take(m_prev) + buf.skip(m_prev).take(k) = buf.take(m_prev + k)
                    let suf = self.0.spec_serialize(v);
                    assert(self.spec_serialize(vs_prev.push(v)) == self.spec_serialize(vs_prev) + suf) by {
                        assert(vs_prev.push(v).drop_last() == vs_prev);
                        assert(vs_prev.push(v).last() == v);
                    };
                    assert(suf == buf.skip(m_prev as int).take(k as int));
                    // m_prev >= 0 and m_prev <= buf.len() from IH
                    self.lemma_parse_length_helper(buf, (n - 1) as usize);
                    self.0.lemma_parse_length(buf.skip(m_prev as int));
                    let m = m_prev as int;
                    let kk = k as int;
                    // m >= 0 from parse_length_helper, kk >= 0 from parse_length
                    assert(buf.take(m) + buf.skip(m).take(kk) =~= buf.take(m + kk));
                }
            }
        }
    }

    proof fn lemma_prefix_secure_helper(&self, s1: Seq<u8>, s2: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(s1, n) is Some ==> self.spec_parse_helper(s1.add(s2), n)
                == self.spec_parse_helper(s1, n),
        decreases n,
    {
        if n > 0 && self.spec_parse_helper(s1, n) is Some {
            self.lemma_prefix_secure_helper(s1, s2, (n - 1) as usize);
            self.lemma_parse_length_helper(s1, (n - 1) as usize);
            if let Some((m, vs)) = self.spec_parse_helper(s1, (n - 1) as usize) {
                assert(s1.add(s2).skip(m as int) =~= s1.skip(m as int) + s2);
                self.0.lemma_prefix_secure(s1.skip(m as int), s2);
            }
        }
    }

    proof fn lemma_parse_length_helper(&self, s: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(s, n) matches Some((m, _)) ==> 0 <= m <= s.len(),
        decreases n,
    {
        if n > 0 {
            self.lemma_parse_length_helper(s, (n - 1) as usize);
            if let Some((m, _)) = self.spec_parse_helper(s, (n - 1) as usize) {
                self.0.lemma_parse_length(s.skip(m as int));
            }
        }
    }

    proof fn lemma_parse_productive_helper(&self, s: Seq<u8>, n: usize)
        requires
            self.requires(),
            self.1 > 0,
            self.0.is_productive(),
        ensures
            n > 0 ==> (self.spec_parse_helper(s, n) matches Some((consumed, _)) ==> consumed > 0),
        decreases n,
    {
        if n > 0 {
            if n == 1 {
                // spec_parse_helper(s, 1):
                //   spec_parse_helper(s, 0) = Some((0, seq![]))
                //   self.0.spec_parse(s.skip(0)) = self.0.spec_parse(s)  [since s.skip(0) = s]
                //   if Some((k, v)), consumed = 0 + k = k > 0 (by productivity)
                assert(s.skip(0int) =~= s);
                self.0.lemma_parse_productive(s);
                // spec_parse_helper(s, 1) definition:
                assert(self.spec_parse_helper(s, 1usize) ==
                    (match self.0.spec_parse(s) {
                        Some((k, v)) => Some((0int + k, seq![].push(v))),
                        None => None,
                    })
                ) by { reveal_with_fuel(RepeatN::spec_parse_helper, 2); };
            } else {
                // n > 1: by IH on n-1, consumed_prev > 0.
                // spec_parse_helper(s, n) = Some((consumed_prev + k, ...)), total > 0.
                self.lemma_parse_productive_helper(s, (n - 1) as usize);
                // IH: spec_parse_helper(s, n-1) matches Some((m, _)) ==> m > 0
                // spec_parse_helper(s, n) = Some((m + k, ...)) with m > 0, k >= 0.
                // self.0.spec_parse(s.skip(m)) gives k >= 0 from parse_length.
                if let Some((consumed, _)) = self.spec_parse_helper(s, n) {
                    // consumed = m + k where m > 0 (from IH) and k >= 0 (from parse_length)
                    if let Some((m, vs)) = self.spec_parse_helper(s, (n - 1) as usize) {
                        assert(m > 0);
                        // spec_parse_helper(s, n) = Some((m + k, ...))
                        // Since spec_parse_helper is closed, use reveal_with_fuel to unfold
                        assert(consumed >= m) by {
                            reveal_with_fuel(RepeatN::spec_parse_helper, 1);
                            self.0.lemma_parse_length(s.skip(m as int));
                        };
                        assert(consumed > 0);
                    }
                }
            }
        }
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for RepeatN<C> {
    type Type = Seq<C::Type>;

    open spec fn requires(&self) -> bool {
        &&& self.0.requires()
        &&& C::is_prefix_secure()
    }

    open spec fn wf(&self, vs: Self::Type) -> bool {
        &&& vs.len() == self.1
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.spec_parse_helper(s, self.1)
    }

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |acc: Seq<u8>, v| acc + self.0.spec_serialize(v))
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {
    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.1 > 0 && self.0.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, vs: Self::Type) {
        if self.wf(vs) {
            self.theorem_serialize_parse_roundtrip_helper(vs, self.1)
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.theorem_parse_serialize_roundtrip_helper(buf, self.1)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if C::is_prefix_secure() {
            self.lemma_prefix_secure_helper(s1, s2, self.1)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.lemma_parse_length_helper(s, self.1)
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if self.is_productive() {
            self.lemma_parse_productive_helper(s, self.1)
        }
    }
}

impl<C: SecureSpecCombinator> RepeatN<C> {
    spec fn parse_correct(
        &self,
        s: Seq<u8>,
        n: usize,
        res: Result<(usize, Seq<C::Type>), ParseError>,
    ) -> bool {
        &&& res matches Ok((k, v)) ==> self.spec_parse_helper(s, n) == Some((k as int, v))
        &&& self.spec_parse_helper(s, n) matches Some((k, v)) ==> res == Ok::<_, ParseError>(
            (k as usize, v),
        )
        &&& res is Err ==> self.spec_parse_helper(s, n) is None
        &&& self.spec_parse_helper(s, n) is None ==> res is Err
    }

    proof fn lemma_spec_serialize_max_length(&self, vs: Seq<C::Type>, n: usize)
        requires
            self.requires(),
            self.wf_helper(vs, n),
            self.spec_serialize(vs).len() <= usize::MAX,
        ensures
            forall|i: int|
                #![auto]
                0 <= i < vs.len() ==> self.0.spec_serialize(vs[i]).len() <= usize::MAX,
            forall|i: int|
                #![auto]
                0 <= i < vs.len() ==> self.spec_serialize(vs.take(i as int)).len() <= usize::MAX,
        decreases vs.len(),
    {
        if vs.len() > 0 {
            let vs_prev = vs.drop_last();
            let v_last = vs.last();
            let suf = self.0.spec_serialize(v_last);

            assert(self.spec_serialize(vs) == self.spec_serialize(vs_prev) + suf) by {
                assert(vs.drop_last() == vs_prev);
                assert(vs.last() == v_last);
            };
            assert(self.spec_serialize(vs_prev).len() <= usize::MAX);
            assert(suf.len() <= usize::MAX);

            assert(self.wf_helper(vs_prev, (n - 1) as usize));
            self.lemma_spec_serialize_max_length(vs_prev, (n - 1) as usize);

            // For i < vs.len() - 1: vs[i] = vs_prev[i], vs.take(i) = vs_prev.take(i)
            assert forall|i: int| 0 <= i < vs.len() implies self.0.spec_serialize(#[trigger] vs[i]).len() <= usize::MAX by {
                if i < vs.len() - 1 {
                    assert(vs[i] == vs_prev[i]);
                } else {
                    // i = vs.len() - 1, vs[i] = v_last
                    assert(vs[i] == v_last);
                }
            };

            assert forall|i: int| 0 <= i < vs.len() implies self.spec_serialize(#[trigger] vs.take(i as int)).len() <= usize::MAX by {
                if i < vs.len() - 1 {
                    assert(vs.take(i as int) == vs_prev.take(i as int));
                } else {
                    // i = vs.len() - 1, vs.take(i) = vs_prev
                    assert(vs.take(i as int) == vs_prev);
                }
            };
        }
    }

    proof fn lemma_spec_serialize_max_length_2(&self, vs: Seq<C::Type>, n: usize)
        requires
            self.requires(),
            self.wf_helper(vs, n),
            self.spec_serialize(vs).len() <= usize::MAX,
        ensures
            forall|i: int|
                #![auto]
                0 <= i <= vs.len() ==> {
                    &&& self.spec_serialize(vs.take(i as int)).len() <= usize::MAX
                },
    {
        self.lemma_spec_serialize_max_length(vs, n);
        // For i == vs.len(): vs.take(vs.len()) == vs
        assert(vs.take(vs.len() as int) == vs);
    }
}

impl<I, O, C, 'x> Combinator<'x, I, O> for RepeatN<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O, SType = &'x <C as Combinator<'x, I, O>>::Type>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    <C as Combinator<'x, I, O>>::Type: 'x,
 {
    type Type = RepeatResult<C::Type>;

    type SType = &'x RepeatResult<C::Type>;

    fn length(&self, vs: Self::SType) -> usize {
        let mut len = 0;
        proof {
            self@.lemma_spec_serialize_max_length(vs@, self.1);
            self@.lemma_spec_serialize_max_length_2(vs@, self.1);
        }
        for i in 0..vs.0.len()
            invariant
                0 <= i <= vs.0.len(),
                self@.wf(vs@),
                self.ex_requires(),
                self@.requires(),
                self@.spec_serialize(vs@).len() <= usize::MAX,
                forall|i: int|
                    0 <= i < vs@.len() ==> self@.0.spec_serialize(#[trigger] vs@[i]).len()
                        <= usize::MAX,
                forall|i: int|
                    0 <= i <= vs@.len() ==> self@.spec_serialize(
                        #[trigger] vs@.take(i as int),
                    ).len() <= usize::MAX,
                len == self@.spec_serialize(vs@.take(i as int)).len(),
            decreases vs.0.len() - i,
        {
            let v = &vs.0[i];
            assert(v@ == vs@[i as int]);
            assert(vs@.take((i + 1) as int).drop_last() == vs@.take(i as int));
            len += self.0.length(v);
        }
        assert(vs@.take(vs.0.len() as int) == vs@);
        len
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires()
    }

    fn parse(&self, input: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (mut s, mut len, mut vs) = (input, 0usize, Vec::new());
        assert(RepeatResult(vs)@ =~= seq![]);

        for i in 0..self.1
            invariant
                0 <= i <= self.1,
                self.ex_requires(),
                self@.requires(),
                0 <= len <= input@.len() <= usize::MAX,
                s@ =~= input@.skip(len as int),  // <-- this is the key
                self@.parse_correct(input@, i, Ok::<_, ParseError>((len, RepeatResult(vs)@))),
            decreases self.1 - i,
        {
            match self.0.parse(s.clone()) {
                Ok((n, v)) => {
                    assert(0 <= n <= input@.skip(len as int).len()) by {
                        self@.0.lemma_parse_length(s@);
                    }
                    let ghost old_vs = RepeatResult(vs)@;
                    vs.push(v);
                    len += n;
                    s = s.subrange(n, s.len());
                    assert(RepeatResult(vs)@ == old_vs.push(v@));
                },
                Err(e) => {
                    proof {
                        self@.lemma_spec_parse_err_unrecoverable(input@, (i + 1) as usize, self.1);
                    }
                    return Err(e);
                },
            }
        }
        Ok((len, RepeatResult(vs)))
    }

    fn serialize(&self, vs: Self::SType, data: &mut O, mut pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let ghost old_data = old(data)@;
        let old_pos = pos;
        assert(data@ == seq_splice(old(data)@, pos, Seq::<u8>::empty()));
        let ghost _vs = vs@;
        for i in 0..vs.0.len()
            invariant
                data@.len() == old_data.len(),
                pos <= data@.len() <= usize::MAX,
                _vs == vs@,
                self@.wf(_vs),
                self.ex_requires(),
                self@.requires(),
                (pos - old_pos) == self@.spec_serialize(_vs.take(i as int)).len(),
                data@ == seq_splice(old_data, old_pos, self@.spec_serialize(_vs.take(i as int))),
        {
            let v = &vs.0[i];
            assert(v@ == _vs[i as int]);
            assert(_vs.take((i + 1) as int).drop_last() == _vs.take(i as int));  // <-- this is the key
            let l = self.0.serialize(v, data, pos)?;
            pos += l;
            assert(data@ == seq_splice(
                old_data,
                old_pos,
                self@.spec_serialize(_vs.take((i + 1) as int)),
            ));
        }
        assert(_vs == _vs.take(vs.0.len() as int));
        Ok(pos - old_pos)
    }
}

/// A combinator to repeatedly parse/serialize the inner combinator C
/// until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer, Repeat fails
pub struct Repeat<C>(pub C);

/// Wrappers around Vec so that their View's can be implemented as DeepView
#[derive(Debug, PartialEq, Eq)]
pub struct RepeatResult<T>(pub Vec<T>);

impl<T: Clone> Clone for RepeatResult<T> {
    fn clone(&self) -> Self {
        RepeatResult(self.0.clone())
    }
}

impl<'x, C: View> Repeat<C> where C::V: SecureSpecCombinator {
    /// Constructs a new `Repeat` combinator, only if the inner combinator is productive.
    pub fn new(c: C) -> (o: Self)
        requires
            c@.is_productive(),
        ensures
            o == Self(c),
    {
        Repeat(c)
    }
}

impl<C: View> View for Repeat<C> {
    type V = Repeat<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        Repeat(self.0@)
    }
}

impl<T: View> View for RepeatResult<T> {
    type V = Seq<T::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

impl<C: SecureSpecCombinator> Repeat<C> {
    #[verusfmt::skip]
    proof fn lemma_serialize_add(&self, v: C::Type, vs: Seq<C::Type>)
        ensures
            self.spec_serialize(seq![v] + vs) == self.0.spec_serialize(v) + self.spec_serialize(vs)
        decreases vs.len(),
    {
        let f = |acc: Seq<u8>, x: C::Type| acc + self.0.spec_serialize(x);
        let all = seq![v] + vs;
        let gv = self.0.spec_serialize(v);

        // fold_left = fold_left_alt for both all and vs
        all.lemma_fold_left_alt(Seq::<u8>::empty(), f);
        vs.lemma_fold_left_alt(Seq::<u8>::empty(), f);

        // all.fold_left_alt(empty, f) = vs.fold_left_alt(f(empty, v), f) = vs.fold_left_alt(gv, f)
        // This follows from the definition: all[0] = v, all.subrange(1, all.len()) = vs
        assert(all[0] == v);
        assert(all.subrange(1, all.len() as int) == vs);
        // By definition of fold_left_alt (single unfolding for all.len() > 0):
        // all.fold_left_alt(empty, f) = all.subrange(1, all.len()).fold_left_alt(f(empty, all[0]), f)
        //                             = vs.fold_left_alt(f(empty, v), f)
        //                             = vs.fold_left_alt(empty + gv, f)
        //                             = vs.fold_left_alt(gv, f)
        assert(all.fold_left_alt(Seq::<u8>::empty(), f) == vs.fold_left_alt(gv, f));

        // vs.fold_left_alt(gv, f) = gv + vs.fold_left_alt(empty, f)
        Self::lemma_fold_left_alt_shift_init(self.0, vs, gv);
    }

    proof fn lemma_fold_left_alt_shift_init(c: C, s: Seq<C::Type>, init: Seq<u8>)
        ensures
            s.fold_left_alt(init, |acc: Seq<u8>, x: C::Type| acc + c.spec_serialize(x))
            == init + s.fold_left_alt(Seq::empty(), |acc: Seq<u8>, x: C::Type| acc + c.spec_serialize(x))
        decreases s.len(),
    {
        let f = |acc: Seq<u8>, x: C::Type| acc + c.spec_serialize(x);
        if s.len() > 0 {
            let x0 = s[0];
            let rest = s.subrange(1, s.len() as int);
            let gx0 = c.spec_serialize(x0);

            // s.fold_left_alt(init, f) = rest.fold_left_alt(init + gx0, f)  [by defn]
            // s.fold_left_alt(empty, f) = rest.fold_left_alt(gx0, f)  [by defn]
            // By IH on rest:
            //   rest.fold_left_alt(init + gx0, f) = (init + gx0) + rest.fold_left_alt(empty, f)
            //   rest.fold_left_alt(gx0, f) = gx0 + rest.fold_left_alt(empty, f)
            // So: s.fold_left_alt(init, f) = (init + gx0) + rest.fold_left_alt(empty, f)
            //                              = init + (gx0 + rest.fold_left_alt(empty, f))
            //                              = init + s.fold_left_alt(empty, f)

            Self::lemma_fold_left_alt_shift_init(c, rest, init + gx0);
            Self::lemma_fold_left_alt_shift_init(c, rest, gx0);
        }
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for Repeat<C> {
    type Type = Seq<C::Type>;

    open spec fn requires(&self) -> bool {
        &&& self.0.requires()
        &&& C::is_prefix_secure()
        &&& self.0.is_productive()
    }

    open spec fn wf(&self, vs: Self::Type) -> bool {
        forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
        decreases s.len(),
    {
        if s.len() == 0 {
            Some((0, seq![]))
        } else {
            match self.0.spec_parse(s) {
                Some((n, v)) => if 0 < n <= s.len() {
                    match self.spec_parse(s.skip(n)) {
                        Some((_, vs)) => Some((s.len() as int, seq![v] + vs)),
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        }
    }

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        RepeatN(self.0, vs.len() as usize).spec_serialize(vs)
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Repeat<C> {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, vs: Self::Type)
        decreases vs.len(),
    {
        if self.wf(vs) {
            if vs.len() == 0 {
                assert(vs == <Seq<C::Type>>::empty());
            } else {
                let (v_, vs_) = (vs.first(), vs.drop_first());
                self.lemma_serialize_add(v_, vs_);  // (0). "re-order" the I.H.
                self.0.theorem_serialize_parse_roundtrip(v_);  // <-- Base
                self.theorem_serialize_parse_roundtrip(vs_);  // <-- I.H.
                let buf0 = self.0.spec_serialize(v_);
                assert(buf0.len() > 0) by {
                    self.0.lemma_serialize_productive(v_);
                }
                let buf1 = self.spec_serialize(vs_);
                let (n0, n1) = (buf0.len() as int, buf1.len() as int);
                assert(seq![v_] + vs_ == vs);  // <-- (1).
                assert(self.spec_serialize(vs) == buf0 + buf1);  // <-- from (0) and (1)
                assert(self.0.spec_parse(buf0) == Some((n0, v_)));  // <-- from Base
                assert(self.spec_parse(buf1) == Some((n1, vs_)));  // <-- from I.H.
                self.0.lemma_prefix_secure(buf0, buf1);
                assert((buf0 + buf1).skip(n0) == buf1);
                assert(self.spec_parse(buf0 + buf1) == Some((n0 + n1, vs)));
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, input: Seq<u8>)
        decreases input.len(),
    {
        if input.len() == 0 {
            assert(input.take(0) == Seq::<u8>::empty());
        } else {
            self.0.theorem_parse_serialize_roundtrip(input);
            match self.0.spec_parse(input) {
                Some((n, v)) => if 0 < n <= input.len() {
                    self.theorem_parse_serialize_roundtrip(input.skip(n));
                    match self.spec_parse(input.skip(n)) {
                        Some((len, vs)) => {
                            assert(self.0.spec_serialize(v) == input.take(n));  // <-- Base
                            assert(self.spec_serialize(vs) == input.skip(n).take(len));  // <-- I.H.
                            self.lemma_serialize_add(v, vs);
                            assert(input.take(n + len) == input.take(n) + input.skip(n).take(len));
                        },
                        None => {},
                    }
                },
                None => {},
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O, C, 'x> Combinator<'x, I, O> for Repeat<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O, SType = &'x <C as Combinator<'x, I, O>>::Type>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    <C as Combinator<'x, I, O>>::Type: 'x,
 {
    type Type = RepeatResult<C::Type>;

    type SType = &'x RepeatResult<C::Type>;

    fn length(&self, vs: Self::SType) -> usize {
        RepeatN(&self.0, vs.0.len()).length(vs)
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires()
    }

    fn parse(&self, input: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let mut vs = Vec::new();
        let mut len: usize = 0;

        assert(input@.take(input@.len() as int) == input@);

        while len < input.len()
            invariant
                0 <= len <= input@.len(),
                self.ex_requires(),
                self@.requires(),
                self@.spec_parse(input@.skip(len as int)) matches Some((_, rest)) ==> {
                    &&& self@.spec_parse(input@) matches Some((_, correct_vs))
                    &&& RepeatResult(vs)@ + rest =~= correct_vs
                },
                len < input@.len() ==> (self@.spec_parse(input@.skip(len as int)) is None
                    ==> self@.spec_parse(input@) is None),
            decreases input@.len() - len,
        {
            let (n, v) = self.0.parse(input.subrange(len, input.len()))?;

            assert(0 < n <= input@.skip(len as int).len()) by {
                self.0@.lemma_parse_productive(input@.skip(len as int));
                self.0@.lemma_parse_length(input@.skip(len as int));
            }

            let ghost prev_len = len;

            vs.push(v);
            len += n;

            assert(input@.skip(prev_len as int).skip(n as int) == input@.skip(len as int));
        }

        Ok((input.len(), RepeatResult(vs)))
    }

    fn serialize(&self, vs: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        RepeatN(&self.0, vs.0.len()).serialize(vs, data, pos)
    }
}

} // verus!
