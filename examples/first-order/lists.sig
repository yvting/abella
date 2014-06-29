sig lists.

kind    i, ilist       type.

type    nl            ilist.
type    cons          i -> ilist -> ilist.

type    ilist         ilist -> o.
type    append        ilist -> ilist -> ilist -> o.
type    rev, perm     ilist -> ilist -> o.
type    select        ilist -> i -> ilist -> o.
