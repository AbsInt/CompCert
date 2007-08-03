% This style produces citations in the `author-year' format.
% It supports two forms of citation: the \cite command produces:  (Author, year)
% in the text; the \cite* command only:  (year) .

 
ENTRY
  { address
    author
    booktitle
    chapter
    edition
    editor
    howpublished
    institution
    journal
    key
    note
    number
    organization
    pages
    publisher
    school
    series
    title
    type
    volume
    year
  }
  {}
  { label extra.label sort.label }
 
INTEGERS { output.state before.all mid.sentence after.sentence
   after.block after.colon }
 
FUNCTION {init.state.consts}
{ #0 'before.all :=
  #1 'mid.sentence :=
  #2 'after.sentence :=
  #3 'after.block :=
  #4 'after.colon :=
}
 
STRINGS { s t }
 
FUNCTION {output.nonnull}
{ 's :=
  output.state mid.sentence =
    { ", " * write$ }
    { output.state after.block =
        { add.period$ write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { output.state after.colon =
              'write$
              { add.period$ " " * write$ }
            if$
            }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}
 
FUNCTION {output.nonnull.extra}
{ 's :=
  output.state mid.sentence =
    { " " * write$ }
    { output.state after.block =
        { add.period$  write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { output.state after.colon =
              'write$
              { add.period$ " " * write$ }
            if$
            }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}
 
FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}
 
FUNCTION {output.extra}
{ duplicate$ empty$
    'pop$
    'output.nonnull.extra
  if$
}
 
FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}
 
FUNCTION {output.check.extra}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull.extra
  if$
}
 
FUNCTION {output.year.check}
{ year empty$
    { "empty year in " cite$ * warning$ }
    { write$
      ": " year * extra.label * 
      mid.sentence 'output.state :=
    }
  if$
}
 
FUNCTION {output.bibitem}
{ newline$
  "\bibitem[" write$
  label write$
  "]{" write$
  cite$ write$
  "}" write$
  newline$
  ""
  before.all 'output.state :=
}
 
FUNCTION {fin.entry}
{ add.period$
  write$
  newline$
}
 
FUNCTION {new.block}
{ output.state before.all =
    'skip$
    { after.block 'output.state := }
  if$
}
 
FUNCTION {new.sentence}
{ output.state after.block =
    'skip$
    { output.state before.all =
        'skip$
        { after.sentence 'output.state := }
      if$
    }
  if$
}
 
FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}
 
FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}
 
FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}
 
FUNCTION {new.block.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.block
  if$
}
 
FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}
 
FUNCTION {boldface}
{ duplicate$ empty$
    { pop$ "" }
    { "{\bf " swap$ * "}" * }
  if$
}
 
FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "{\em " swap$ * "}" * }
  if$
}
 
INTEGERS { nameptr namesleft numnames }
 
FUNCTION {format.names}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
        { s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't := }
        { s nameptr "{vv~}{ll}{, jj}{, f.}" format.name$ 't := }
      if$
      nameptr #1 >
        { namesleft #1 >
            { ", " * t * }
            { numnames #2 >
                { "," * }
                'skip$
              if$
              t "others" =
                { " et~al." * }
                { " and " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}
 
FUNCTION {format.ed.names}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
        { s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't := }
        { s nameptr "{f. }{vv~}{ll}{, jj}" format.name$ 't := }
      if$
      nameptr #1 >
        { namesleft #1 >
            { ", " * t * }
            { numnames #2 >
                { "," * }
                'skip$
              if$
              t "others" =
                { " et~al." * }
                { " and " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { author format.names }
  if$
}
 
FUNCTION {format.key}
{ empty$
    { key field.or.null }
    { "" }
  if$
}

FUNCTION {format.editors}
{ editor empty$
    { "" }
    { editor format.names
      editor num.names$ #1 >
        { " (eds.)" * }
        { " (ed.)" * }
      if$
    }
  if$
}
 
FUNCTION {format.editors.extra}
{ editor empty$
    { "" }
    { editor format.ed.names
      editor num.names$ #1 >
        { " (eds.)" * }
        { " (ed.)" * }
      if$
    }
  if$
}
 
FUNCTION {format.title}
{ title empty$
    { "" }
    { "`" title "'" * * }
  if$
}
 
FUNCTION {n.dashify}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
        { t #1 #2 substring$ "--" = not
            { "--" *
              t #2 global.max$ substring$ 't :=
            }
            {   { t #1 #1 substring$ "-" = }
                { "-" *
                  t #2 global.max$ substring$ 't :=
                }
              while$
            }
          if$
        }
        { t #1 #1 substring$ *
          t #2 global.max$ substring$ 't :=
        }
      if$
    }
  while$
}
 
FUNCTION {first.page.number}
{ 't :=
  ""
    { t "" =
        { #0 }
        { t #1 #1 substring$ "-" = not }
      if$
    }
    { t #1 #1 substring$ *
      t #2 global.max$ substring$ 't :=
    }
  while$
}

FUNCTION {format.btitle}
{ title emphasize
}
 
FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}
 
FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}
 
FUNCTION {format.bvolume}
{ volume empty$
    { "" }
    { "Vol." volume tie.or.space.connect
      series empty$
        'skip$
        { " of " * series emphasize * }
      if$
      "volume and number" number either.or.check
    }
  if$
}
 
FUNCTION {format.number.series}
{ volume empty$
    { number empty$
        { series field.or.null }
        { output.state mid.sentence =
            { "No." }
            { "No." }
          if$
          number tie.or.space.connect
          series empty$
            { "there's a number but no series in " cite$ * warning$ }
            { " in " * series * }
          if$
        }
      if$
    }
    { "" }
  if$
}
 
FUNCTION {format.edition}
{ edition empty$
    { "" }
    { output.state mid.sentence =
        { edition "l" change.case$ " edition" * }
        { edition "t" change.case$ " edition" * }
      if$
    }
  if$
}
 
INTEGERS { multiresult }
 
FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
        { #1 'multiresult := }
        { t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}
 
FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
        { "pp." pages n.dashify tie.or.space.connect }
        { "p." pages tie.or.space.connect }
      if$
    }
  if$
}

FUNCTION {format.page}
{ pages empty$
    { "" }
    { "p.~" pages first.page.number * }
  if$
}

FUNCTION {format.vol.num.pages}
{ volume field.or.null
  volume empty$
    'skip$
    { boldface }
  if$
  number empty$
    'skip$
    { "(" number * ")" * *
      volume empty$
        { "there's a number but no volume in " cite$ * warning$ }
        'skip$
      if$
    }
  if$
  pages empty$
    'skip$
    { duplicate$ empty$
        { pop$ format.pages }
        { ", " * pages n.dashify * }
      if$
    }
  if$
}

FUNCTION {format.vol.num.page}
{ volume field.or.null
  volume empty$
    'skip$
    { boldface }
  if$
  number empty$
    'skip$
    { "(" number * ")" * *
      volume empty$
        { "there's a number but no volume in " cite$ * warning$ }
        'skip$
      if$
    }
  if$
  pages empty$
    'skip$
    { duplicate$ empty$
        { pop$ format.pages }
        { ", " * pages first.page.number * }
      if$
    }
  if$
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    'format.pages
    { type empty$
        { "Chapt." }
        { type "l" change.case$ }
      if$
      chapter tie.or.space.connect
      pages empty$
        'skip$
        { ", " * format.pages * }
      if$
    }
  if$
}
 
FUNCTION {format.in.ed.booktitle}
{ booktitle empty$
    { "" }
    { editor empty$
        { "In: " booktitle emphasize * }
        { "In: " format.editors.extra * ": " * booktitle emphasize * }
      if$
    }
  if$
}
 
FUNCTION {format.in.booktitle.or.series}
{ booktitle empty$
    { series empty$
        { "" }
        { "In: " series emphasize * }
      if$
    }
    { editor empty$
        { "In: " booktitle emphasize * }
        { "In: " format.editors.extra * ": " * booktitle emphasize * }
      if$ 
    }
  if$
}
 
FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
}
 
FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
}
 
FUNCTION {format.article.crossref}
{ "In"
  " \cite{" * crossref * "}" *
}
 
FUNCTION {format.book.crossref}
{ volume empty$
    { "empty volume in " cite$ * "'s crossref of " * crossref * warning$
      "In "
    }
    { "Vol." volume tie.or.space.connect
      " of " *
    }
  if$
  "\cite{" * crossref * "}" *
}
 
FUNCTION {format.incoll.inproc.crossref}
{ "In"
  " \cite{" * crossref * "}" *
}
 
FUNCTION {article}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  crossref missing$
    { journal emphasize "journal" output.check.extra
      format.vol.num.pages output.extra
    }
    { format.article.crossref output.nonnull
      format.pages output
    }
  if$
  new.block
  note output
  fin.entry
}
 
FUNCTION {book}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check
      editor format.key output
    }
    { format.authors output.nonnull
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  output.year.check
  format.btitle "title" output.check
  crossref missing$
    { format.bvolume output
      format.number.series output
      new.block
      address empty$
        'skip$
        { address ": " * output
          after.colon 'output.state :=
        }
      if$
      publisher "publisher" output.check.extra
    }
    { new.block
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  new.block
  note output
  fin.entry
}
 
FUNCTION {booklet}
{ output.bibitem
  format.authors output
  author format.key output
  output.year.check
  format.btitle "title" output.check
  new.block
  howpublished output
  address output
  new.block
  note output
  fin.entry
}
 
FUNCTION {inbook}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check
      editor format.key output
    }
    { format.authors output.nonnull
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  output.year.check
  format.btitle "title" output.check
  crossref missing$
    { format.bvolume output
      format.chapter.pages "chapter and pages" output.check
      format.number.series output
      new.block
      address empty$
        'skip$
        { address ": " * output
          after.colon 'output.state :=
        }
      if$
      publisher "publisher" output.check.extra
    }
    { format.chapter.pages "chapter and pages" output.check
      new.block
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  new.block
  note output
  fin.entry
}
 
FUNCTION {incollection}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.bvolume output
      format.number.series output
      new.block
      address empty$
        'skip$
        { address ": " * output
          after.colon 'output.state :=
        }
      if$
      publisher "publisher" output.check.extra
      format.edition output
      format.chapter.pages output
    }
    { format.incoll.inproc.crossref output.nonnull
      format.chapter.pages output
    }
  if$
  new.block
  note output
  fin.entry
}
 
FUNCTION {inproceedings}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  crossref missing$
    { format.in.booktitle.or.series "booktitle or series" output.check
      format.bvolume output
      new.sentence
      address output
      format.pages output
    }
    { format.incoll.inproc.crossref output.nonnull
      format.pages output
    }
  if$
  publisher output
  new.block
  note output
  fin.entry
}
 
FUNCTION {conference} { inproceedings }
 
FUNCTION {manual}
{ output.bibitem
  format.authors output
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  organization output
  address output
  format.edition output
  new.block
  note output
  fin.entry
}
 
FUNCTION {mastersthesis}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  "Master's thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  new.block
  note output
  fin.entry
}
 
FUNCTION {misc}
{ output.bibitem
  format.authors output
  author format.key output
  output.year.check
  format.title output
  new.block
  howpublished output
  new.block
  note output
  fin.entry
}
 
FUNCTION {phdthesis}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  "Ph.D. thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  new.block
  note output
  fin.entry
}
 
FUNCTION {proceedings}
{ output.bibitem
  format.editors output
  editor format.key output
  output.year.check
  format.title "title" output.check
  format.bvolume output
  format.number.series output
  new.block
  address empty$
     'skip$
     { address ": " * output
       after.colon 'output.state :=
     }
  if$
  organization output.extra
  publisher output
  new.block
  note output
  fin.entry
}
 
FUNCTION {techreport}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  format.tr.number output.nonnull
  institution "institution" output.check
  address output
  new.block
  note output
  fin.entry
}
 
FUNCTION {unpublished}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  output.year.check
  format.title "title" output.check
  new.block
  note "note" output.check
  fin.entry
}
 
FUNCTION {default.type} { misc }

MACRO {jan} {"Jan."}

MACRO {feb} {"Feb."}

MACRO {mar} {"Mar."}

MACRO {apr} {"Apr,"}

MACRO {may} {"May"}

MACRO {jun} {"June"}

MACRO {jul} {"July"}

MACRO {aug} {"Aug."}

MACRO {sep} {"Sept."}

MACRO {oct} {"Oct."}

MACRO {nov} {"Nov."}

MACRO {dec} {"Dec."}

READ
 
FUNCTION {sortify}
{ purify$
  "l" change.case$
}
 
INTEGERS { len }
 
FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}
 
FUNCTION {format.lab.names}
{ 's :=
  s #1 "{vv~}{ll}" format.name$
  s num.names$ duplicate$
  #2 >
    { pop$ " et~al." * }
    { #2 <
        'skip$
        { s #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
            { " et~al." * }
            { " and " * s #2 "{vv~}{ll}" format.name$ * }
          if$
        }
      if$
    }
  if$
}
 
FUNCTION {author.key.label}
{ author empty$
    { key empty$
        { cite$ #1 #3 substring$ }
        'key
      if$
    }
    { author format.lab.names }
  if$
}
 
FUNCTION {author.editor.key.label}
{ author empty$
    { editor empty$
        { key empty$
            { cite$ #1 #3 substring$ }
            'key
          if$
        }
        { editor format.lab.names }
      if$
    }
    { author format.lab.names }
  if$
}
 
FUNCTION {editor.key.label}
{ editor empty$
    { key empty$
        { cite$ #1 #3 substring$ }
        'key
      if$
    }
    { editor format.lab.names }
  if$
}
 
FUNCTION {calc.label}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.key.label
    { type$ "proceedings" =
        'editor.key.label
        'author.key.label
      if$
    }
  if$
  "\protect\citeauthoryear{" swap$ * "}{"
  *
  year field.or.null purify$ #-1 #4 substring$
  *
  'label :=
}
 
FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
        { "   " * }
        'skip$
      if$
      s nameptr "{vv{ } }{ll{ }}{  f{ }}{  jj{ }}" format.name$ 't :=
      nameptr numnames = t "others" = and
        { "et al" * }
        { t sortify * }
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}
 
FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}
 
FUNCTION {author.sort}
{ author empty$
    { key empty$
        { "to sort, need author or key in " cite$ * warning$
          ""
        }
        { key sortify }
      if$
    }
    { author sort.format.names }
  if$
}
 
FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
        { key empty$
            { "to sort, need author, editor, or key in " cite$ * warning$
              ""
            }
            { key sortify }
          if$
        }
        { editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}
 
FUNCTION {editor.sort}
{ editor empty$
    { key empty$
        { "to sort, need editor or key in " cite$ * warning$
          ""
        }
        { key sortify }
      if$
    }
    { editor sort.format.names }
  if$
}
 
FUNCTION {presort}
{ calc.label
  label sortify
  "    "
  *
  type$ "book" =
  type$ "inbook" =
  or
    'author.editor.sort
    { type$ "proceedings" =
        'editor.sort
        'author.sort
      if$
    }
  if$
  #1 entry.max$ substring$
  'sort.label :=
  sort.label
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  'sort.key$ :=
}
 
ITERATE {presort}
 
SORT            % by label, sort.label, title---for final label calculation
 
STRINGS { last.label next.extra }
 
INTEGERS { last.extra.num }
 
FUNCTION {initialize.extra.label.stuff}
{ #0 int.to.chr$ 'last.label :=
  "" 'next.extra :=
  #0 'last.extra.num :=
}
 
FUNCTION {forward.pass}
{ last.label label =
    { last.extra.num #1 + 'last.extra.num :=
      last.extra.num int.to.chr$ 'extra.label :=
    }
    { "a" chr.to.int$ 'last.extra.num :=
      "" 'extra.label :=
      label 'last.label :=
    }
  if$
}
 
FUNCTION {reverse.pass}
{ next.extra "b" =
    { "a" 'extra.label := }
    'skip$
  if$
  label extra.label * "}" * 'label :=
  extra.label 'next.extra :=
}
 
EXECUTE {initialize.extra.label.stuff}
 
ITERATE {forward.pass}
 
REVERSE {reverse.pass}
 
FUNCTION {bib.sort.order}
{ sort.label
  "    "
  *
  year field.or.null sortify
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  'sort.key$ :=
}
 
ITERATE {bib.sort.order}
 
SORT            % by sort.label, year, title---giving final bibliography order
 
FUNCTION {begin.bib}
{ preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{}" write$ newline$
}
 
EXECUTE {begin.bib}
 
EXECUTE {init.state.consts}
 
ITERATE {call.type$}
 
FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$
}
 
EXECUTE {end.bib}


