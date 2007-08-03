%%
%% This is file `kluwer.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% kluwer.dtx  (with options: `head')
%% klumac.sty  (with options: `head')
%% klu11.clo  (with options: `head')
%% klulist.sty  (with options: `head')
%% kluopen.sty  (with options: `head')
%% kluedit.sty  (with options: `head')
%% klutab.sty  (with options: `head')
%% klufloa.sty  (with options: `head')
%% klunote.sty  (with options: `head')
%% kluref.sty  (with options: `head')
%% klumath.sty  (with options: `head')
%% klusec.sty  (with options: `head')
%% kluwer.dtx  (with options: `neck')
%% klumac.sty  (with options: `neck')
%% klumac.sty  (with options: `main')
%% klu11.clo  (with options: `main')
%% klulist.sty  (with options: `main')
%% kluopen.sty  (with options: `main')
%% kluedit.sty  (with options: `main')
%% klutab.sty  (with options: `main')
%% klufloa.sty  (with options: `main')
%% klunote.sty  (with options: `main')
%% kluref.sty  (with options: `main')
%% klumath.sty  (with options: `main')
%% klusec.sty  (with options: `main')
%% kluwer.dtx  (with options: `tail')
%% 
%% IMPORTANT NOTICE:
%% 
%% For the copyright see the source file.
%% 
%% Any modified versions of this file must be renamed
%% with new filenames distinct from kluwer.cls.
%% 
%% For distribution of the original source see the terms
%% for copying and modification in the file kluwer.dtx klumac.sty klu11.clo klulist.sty kluopen.sty kluedit.sty klutab.sty klufloa.sty klunote.sty kluref.sty klumath.sty klusec.sty kluwer.dtx klumac.sty klumac.sty klu11.clo klulist.sty kluopen.sty kluedit.sty klutab.sty klufloa.sty klunote.sty kluref.sty klumath.sty klusec.sty kluwer.dtx.
%% 
%% This generated file may be distributed as long as the
%% original source files, as listed above, are part of the
%% same distribution. (The sources need not necessarily be
%% in the same archive or directory.)
\def\filedate{2000/04/29}
\def\kluclassname{kluwer}
\def\kluclassversion{1.3} % option kaplist turned on for 1.2
\def\klujnlname{none}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{kluwer}[\filedate\space \kluclassversion\space
    Kluwer base document class]
\newcommand\@ptsize{}
\newcommand\@pttensize{1}
\newif\if@restonecol
\newif\if@openright

\DeclareOption{a4paper}
   {\setlength\paperheight {297mm}%
    \setlength\paperwidth  {210mm}}
\DeclareOption{a5paper}
   {\setlength\paperheight {210mm}%
    \setlength\paperwidth  {148mm}}
\DeclareOption{b5paper}
   {\setlength\paperheight {250mm}%
    \setlength\paperwidth  {176mm}}
\DeclareOption{letterpaper}
   {\setlength\paperheight {11in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{legalpaper}
   {\setlength\paperheight {14in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{executivepaper}
   {\setlength\paperheight {10.5in}%
    \setlength\paperwidth  {7.25in}}
\DeclareOption{landscape}
   {\setlength\@tempdima   {\paperheight}%
    \setlength\paperheight {\paperwidth}%
    \setlength\paperwidth  {\@tempdima}}
\DeclareOption{9pt}{\renewcommand\@pttensize{}\renewcommand\@ptsize{9}}
\DeclareOption{10pt}{\renewcommand\@ptsize{0}}
\DeclareOption{11pt}{\renewcommand\@ptsize{1}}
\DeclareOption{12pt}{\renewcommand\@ptsize{2}}
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\DeclareOption{openright}{\@openrighttrue}
\DeclareOption{draft}{\setlength\overfullrule{5pt}}
\DeclareOption{final}{\setlength\overfullrule{0pt}}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\@twocolumntrue}
\ExecuteOptions{a4paper,11pt,twoside,onecolumn,final,openright}




\font\@klusymfont=cmr10
\DeclareOption{klusym}{\font\@klusymfont=klusym10 }
\newif\if@kaplist
\DeclareOption{kaplist}{\@kaplisttrue}
\newif\if@margspec
\DeclareOption{margspec}{\@margspectrue}
\newif\if@copyrighthead  \@copyrightheadfalse
\newif\if@kapidenthead   \@kapidentheadfalse
\newif\if@noid           \@noidfalse
\DeclareOption{copyrighthead}{\@copyrightheadtrue}
\DeclareOption{kapidenthead}{\@kapidentheadtrue}
\DeclareOption{noid}{\@noidtrue}
\newif\if@numreferences
\DeclareOption{namedreferences}{\@numreferencesfalse}
\DeclareOption{numreferences}{\@numreferencestrue}
\DeclareOption{openbib}{}
\ExecuteOptions{namedreferences}
\let\@EndKlumathook\@empty
\def\AtEndKluMath{\g@addto@macro\@EndKlumathook}

\DeclareOption{leqno}{\AtEndKluMath{\varleqno}}
\DeclareOption{fleqn}{\AtEndKluMath{\varfleqn}}
\DeclareOption{mathsec}{%
   \def\theequation{\arabic{section}.\arabic{equation}}}
\DeclareOption{mathchap}{%
   \def\theequation{\arabic{chapter}.\arabic{equation}}}
\newif\if@thms \@thmsfalse
\DeclareOption{thms}{\@thmstrue }
\DeclareOption{secthm}{\AtEndKluMath{\if@thms
    \renewcommand{\thethm}{\thesection.\arabic{thm}.}%
    \renewcommand{\thecrit}{\thesection.\arabic{crit}.}%
    \renewcommand{\therem}{\thesection.\arabic{rem}.}%
    \renewcommand{\theNote}{\thesection.\arabic{Note}.}%
    \renewcommand{\thesumm}{\thesection.\arabic{summ}.}%
    \renewcommand{\thecase}{\thesection.\arabic{case}.}%
    \fi
    }}
\newif\if@chapterdef  \@chapterdeffalse
\DeclareOption{chapter}{\@chapterdeftrue }


\ProcessOptions % including options for modules


\IfFileExists{amssymb.sty}{\RequirePackage[psamsfonts]{amssymb}%
    \global\font\smallmsa=msam7
    \gdef\Register{$^{\mbox{\smallmsa\char114}}$~}}{}
\IfFileExists{wasysym.sty}{\RequirePackage{wasysym}}{%
  \IfFileExists{wasysym.tex}{\input{wasysym}}{}}
\def\I{{\bf I}}
\newcommand\iduaal{\overline{\I}}
\let\forces\Vdash
\newcommand\rrestrict{\hbox{$\mid$ \kern-5pt \raise3.6pt\hbox{$
                      \scriptscriptstyle \backslash$}}}
\newcommand\restrict{\mathrel{\mathpalette\rrestrict{}}}
\let\diamond\lozenge
\newcommand\concat{\mathrel{\raise1pt\hbox{$\!\!^\frown\!\!$}}}
\newcommand\lh{\mathop\mathrm{lh}}
\newcommand\depth{\mathop\mathrm{depth}}
\newcommand\dom{\mathop\mathrm{dom}}
\newcommand\range{\mathop\mathrm{range}}
\newcommand\mapright[1]{\smash{\mathop{\longrightarrow}\limits^{#1}}}
\newcommand\mapdown[1]{\big\downarrow
                       \rlap{$\vcenter{\hbox{$\scriptstyle#1$}}$}}
\newcommand{\dC}{C \! \! \! \! {\scriptscriptstyle {}^{{}_|}}\ }
\newcommand{\dL}{I \! \! L}
\newcommand{\dE}{I \! \! E}
\newcommand{\dF}{I \! \! F}
\newcommand{\dP}{I \! \! P}
\newcommand{\dN}{I \! \! N}
\newcommand{\dR}{I \! \! R}
\newcommand{\dZ}{Z \! \! \! Z}
\newcommand{\dQ}{Q \! \! \! \! {\scriptscriptstyle {}^|}\ }
\newcommand{\nequiv}{\mathrel{\setbox0\hbox{$\equiv$}%
                     \rlap{\hbox{$\equiv$}}\hbox to \wd0{\hfil $/$\hfil}}}
\newcommand{\lsim}{\mathrel{\rlap{\raise -.3ex\hbox{${\scriptstyle\sim}$}}%
                   \raise .6ex\hbox{${\scriptstyle <}$}}}%
\newcommand{\gsim}{\mathrel{\rlap{\raise -.3ex\hbox{${\scriptstyle\sim}$}}%
                   \raise .6ex\hbox{${\scriptstyle >}$}}}%
\newcommand{\logr}{\mathrel{\rlap{\raise -.3ex\hbox{${\scriptstyle <}$}}%
                   \raise .6ex\hbox{${\scriptstyle >}$}}}%
\newcommand{\grlo}{\mathrel{\rlap{\raise -.3ex\hbox{${\scriptstyle >}$}}%
                   \raise .6ex\hbox{${\scriptstyle <}$}}}%
\newcommand{\oast}{\setbox0\hbox{$\odot$}%
                   \rlap{\hbox to \wd0{\hfil$\ast$\hfil}}\box0}
\newcommand{\res}{\oalign{\hbox{$\grave{}$\kern-3pt$\mid$}}}
\newcommand{\dres}{\mid \! \res}
\newcommand{\bigo}[1]{\setbox0\hbox{$\bigcirc$}%
             \rlap{\raise .2ex\hbox to \wd0{\hfil ${\scriptscriptstyle
                   #1}$\hfil}}\box0}
\newcommand{\Res}[1]{\mathop{\hbox{Res}}\limits_{\scriptscriptstyle #1}}
\newcommand{\down}[1]{\raise -1ex\hbox{{$\scriptstyle #1$}}}
\newcount\@cla
\newcount\@clb
\hyphenation{equiv-a-lent equiv-a-lent-ly sat-is-fy sat-is-fies
             sat-is-fied}
\newcommand\fn{\hspace*{14pt} \= \kill}
\newcommand\mc{\multicolumn}
\newcommand{\dummy}[1]{}
\def\today{\ifcase\month\or January\or February\or March\or April\or
   May\or June\or July\or August\or September\or October\or November\or
   December\fi \space\number\day, \number\year}
\def\TODAY{\number\day/\ifcase\month\or 01\or 02\or 03\or 04\or 05\or
    06\or 07\or 08\or 09\or 10\or 11\or 12\fi/\number\year}
\def\timenow{%
  \@tempcnta=\time \divide\@tempcnta by 60 \number\@tempcnta:\multiply
  \@tempcnta by 60 \@tempcntb=\time \advance\@tempcntb by -\@tempcnta
  \ifnum\@tempcntb <10 0\number\@tempcntb\else\number\@tempcntb\fi}
\def\numtoword#1{\ifcase#1\or one\or two\or three\or four\or
  five\or six\or seven\or eight\or nine\or ten\or eleven\or twelve\or
  thirteen\or fourteen\or fifteen\or sixteen\or seventeen\or
  eighteen\or nineteen\or twenty\fi}
\def\NUMTOWORD#1{\ifcase#1\or ONE\or TWO\or THREE\or FOUR\or
  FIVE\or SIX\or SEVEN\or EIGHT\or NINE\or TEN\or ELEVEN\or TWELVE\or
  THIRTEEN\or FOURTEEN\or FIFTEEN\or SIXTEEN\or SEVENTEEN\or
  EIGHTEEN\or NINETEEN\or TWENTY\fi}

\def\ifempty#1#2#3{\def\inner{#1}\ifx\inner\empty
   #2\else #3\fi }
\def\ifdef#1{\edef\tempa{\expandafter\@gobble\string #1}%
   \expandafter\expandafter\expandafter\ifx\expandafter\csname
   \tempa \endcsname\relax
   \let\next\nosw \else \let\next=\yessw \fi \next}
\def\nosw{\iffalse}
\def\yessw{\iftrue}
\newif\ifklaar
\newbox\bdj
\def\onestep#1{\ifklaar\else
           \if#1){)}\klaartrue\else
           \if#1.{.}\klaartrue\else
           \if#1]{]}\klaartrue\else
           \if#1-{--}\klaartrue\else
           \if#1*{*}\klaartrue\else
           #1%
           \fi\fi\fi\fi\fi
               \fi}
\def\subspitem#1{\scan#1\end}
\def\spitem#1 {%
  \def\scan##1##2\end{\def\aux{##1}%
     \ifklaar\global\setbox\bdj=\hbox{##1##2\space}\else
     \ifx\aux\empty \else \def\aux{##2}\onestep{##1}%
     \ifx\aux\empty \else \scan##2\end \fi \fi \fi}%
  \global\setbox\bdj\hbox{}%
  \klaarfalse\expandafter\item[\subspitem{#1}]%
  \unhbox\bdj}
\font\genacc=cmr10
\def\genaccent#1#2#3#4#5{\protect\@genaccent{#1}{#2}{#3}{#4}{#5}}
\def\@genaccent#1#2#3#4#5{%
   \leavevmode\setbox0=\hbox{#3}%
   \vbox{\offinterlineskip
   \ifempty{#1}{}{%\else
    \hbox to\wd0{\hss\genacc \char#1\hss}}%
    \ifempty{#4}{\kern -.8ex}{\kern #4}%
   \vbox to\ht0{\copy0\vss}%
   \vtop{\null\vbox to\dp0{\vss}%
   \ifempty{#2}{}{%\else
     \ifempty{#5}{\kern .2ex}{\kern#5}%
     \hbox to \wd0{\hss \genacc\char #2\hss}}%
    }}}
\renewcommand\.[1]{\genaccent{95}{}{#1}{}{}}
\newcommand\BlackBox{\hbox{\@klusymfont B}~}
\newcommand\EmptyBox{\hbox{\@klusymfont E}~}
\newcommand\HstripeBox{\hbox{\@klusymfont H}~}
\newcommand\VstripeBox{\hbox{\@klusymfont V}~}
\newcommand\LstripeBox{\hbox{\@klusymfont L}~}
\newcommand\RstripeBox{\hbox{\@klusymfont R}~}
\newcommand\UpCrossBox{\hbox{\@klusymfont U}~}
\newcommand\DiagCrossBox{\hbox{\@klusymfont D}~}
\def\cb{\@ifnextchar[{\@cbone}{\@cbone[8pc]}}
\def\@cbone[#1]#2{{\setbox0\hbox{#2}%
     \ifdim\wd0 >#1 \parbox[t]{#1}{#2}\else #2\fi}}
\def\nbox#1#2#3#4#5#6{\begingroup\setbox0\hbox{0}%
    \ifempty{#1}{\hfil #2}{\hbox to #1\wd0{\hfil #2}}%
    \ifempty{#3}{\hbox{#4}}{\hbox to #3\wd0{\hfil #4\hfil }}%
    \ifempty{#5}{#6 \hfil}{\hbox to #5\wd0{#6\hfil }}%
    \endgroup}
\newif\ifkern@mathmode \kern@mathmodefalse
\def\charkerncharspace{\kern 0.5ex}
\def\charkernwordspace{\kern 0.5em\penalty 10}
\let\charkerncommand\uppercase
\def\@kap@tfor#1:=#2\do#3{\ifempty{#1}{}{%
  \@tforloop#2\@nil\@nil\@@#1{#3}}}
\def\charkern#1{%
    \ifempty{#1}{}{%else
  \begingroup
  \def\test##1##2!!!!{\def\@tempa{##2}}\test#1!!!!%
  \ifx\@tempa\empty \edef\@@kc{#1}\else \def\@@kc{#1}\fi
  \def\c@@k{@s@e@v@y}%
  \def\ck@@##1 @s@e@v@y\@@ck{\def\@@kc{##1}}%
  \def\ck@##1 ##2\@@ck{\def\@kc{##1}\def\@@kc{##2}}%
  \def\iterate{\expandafter\expandafter\expandafter\ck@
    \expandafter\@@kc\space @s@e@v@y\@@ck
    \expandafter\@kernword\expandafter{\@kc}%
    \ifx\@@kc\c@@k
      \let\next\relax
    \else
      \expandafter\ck@@\@@kc\@@ck
      \let\next\iterate\charkernwordspace
    \fi\next}\iterate
  \endgroup
  }}

\def\@kernword#1{\def\d@ll@rm@th{$}\@kap@tfor\@nextchar:=#1\do{%
    \ifx\@nextchar\d@ll@rm@th
      \ifkern@mathmode
        \kern@mathmodefalse
        $\kern@math$%
      \else
        \kern@mathmodetrue
        \xdef\kern@math{}%
      \fi
    \else
      \ifkern@mathmode
        \begingroup
          \def\protect{\noexpand}%
          \xdef\kern@math{\kern@math\@nextchar}%
        \endgroup
      \else
          \charkerncommand\expandafter{\@nextchar}\charkerncharspace
      \fi
    \fi
}}

\newcount\tracingkluwer
\def\kludebug#1{\relax\ifcase\tracingkluwer \or
    \wlog{kap: #1}\or \typeout{kap: #1}\else
    \immediate\wlog{kap*: #1}\typeout{kap: #1}\fi}
\global\tracingkluwer=3
\def\kluverbatim{\par\begingroup\vbox \bgroup\trivlist
    \item\relax \vskip\parskip
    \rightskip\z@skip \parindent\z@
    \parfillskip\@flushglue \parskip0pt \@@par \@tempswafalse
    \def\par{\if@tempswa \leavevmode\null\@@par\penalty\interlinepenalty
    \else \@tempswatrue \ifhmode\@@par\penalty\interlinepenalty\fi \fi}
    \let\do\@makeother \catcode`\|=0
    \obeylines \verbatim@font \@noligs \dospecials \catcode`\%=14
    \frenchspacing\@vobeyspaces
    \everypar \expandafter{\the\everypar \unpenalty }}
\def\endkluverbatim{\endtrivlist\egroup\endgroup}
\renewcommand\normalsize{%
   \@setfontsize\normalsize\@xipt{13}%
   \abovedisplayskip 10\p@ \@plus 2\p@ \@minus5\p@
   \abovedisplayshortskip \z@ \@plus 3\p@
   \belowdisplayshortskip 6\p@ \@plus 3\p@ \@minus3\p@
   \belowdisplayskip \abovedisplayskip
   \let\@listi\@listI}
\normalsize
\newcommand\small{%
   \@setfontsize\small\@xpt\@xiipt
   \abovedisplayskip 9\p@ \@plus3\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus2\p@
   \belowdisplayshortskip 5\p@ \@plus2\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 4\p@ \@plus2\p@ \@minus2\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\footnotesize{%
   \@setfontsize\footnotesize\@ixpt\@xipt
   \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3\p@ \@plus\p@ \@minus\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\scriptsize{\@setfontsize\scriptsize\@viiipt{9.5}}
\newcommand\little{\@setfontsize\little\@viipt\@viiipt}
\newcommand\tiny{\@setfontsize\tiny\@vipt\@viipt}
\newcommand\large{\@setfontsize\large\@xiipt{14}}
\newcommand\Large{\@setfontsize\Large\@xivpt{18}}
\newcommand\LARGE{\@setfontsize\LARGE\@xviipt{22}}
\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}
\setlength\hoffset{-1in}
\setlength\voffset{0pt}
\setlength\parindent {14\p@}
\setlength\headheight{12\p@}
\setlength\headsep   {13\p@}
\setlength\topskip   {10\p@}
\setlength\footskip  {27.5\p@}
\setlength\marginparsep{10pt}
\setlength\marginparpush{5\p@}
\setlength\maxdepth  {.5\topskip}
\setlength\@maxdepth\maxdepth
\setlength\columnsep{10pt}
\setlength\columnseprule{0pt}
\setlength\fboxsep{3pt}
\setlength\fboxrule{.4pt}
\newdimen\id@boxheight
\AtBeginDocument{%
  \setlength\@tempdima{\paperwidth}%
  \addtolength\@tempdima{-\textwidth}%
  \divide\@tempdima by 2
  \setlength\@tempdimb\marginparwidth
  \addtolength\@tempdimb\marginparsep
  \addtolength\@tempdimb{2pc}%
  \ifdim \@tempdima <\@tempdimb
     \@settopoint\@tempdimb
     \GenericError{Pointsize}{Pointsize Error: Marginpars disabled}{}{You made
      your \string\textwidth\space (\the\textwidth) and
      \string\marginparwidth (\the\marginparwidth) too wide.\MessageBreak
      The allowed value for margin space: (\the\@tempdima). Needed value:
      (\the\@tempdimb).\MessageBreak
      This is not enough,
      so I will set \string\marginparwidth\space  to 0pt.\MessageBreak
      Let's hope that fixes it.
     }%
     \marginparwidth \z@
     \marginparsep \z@
  \fi
  \ifdim \@tempdima <2pc
     \@tempdimb=\paperwidth
     \advance\@tempdimb by -4pc
     \@settopoint\@tempdimb
     \GenericError{Pointsize}{Pointsize Error: Invalid sizes given}{}{You
     made your \string\textwidth\space (\the\textwidth)
     wider than the available total\MessageBreak
     (Which is: \the\@tempdimb). Please press X and try again.
     }%
  \fi
  \oddsidemargin \@tempdima
  \evensidemargin \@tempdima
  \setlength\@tempdima{\paperheight}
  \addtolength\@tempdima{-\footskip}
  \addtolength\@tempdima{-\headheight}
  \addtolength\@tempdima{-\headsep}
  \setlength\@tempdimb{\@tempdima}
  \addtolength\@tempdima{-\textheight}
  \divide\@tempdima by 2
  \ifdim \@tempdima <2pc
  \advance\@tempdimb by -4pc
  \@settopoint\@tempdimb
     \GenericError{Pointsize}{Pointsize Error: Invalid sizes given}{}{You
     made your \string\textheight\space (\the\textheight)
     more than the available total.\MessageBreak
     (Which is: \the\@tempdimb). Please press X and try again.
     }%
  \fi
  \setlength\topmargin{0pt}
  \setlength\id@boxheight{\@tempdima}
  \advance\id@boxheight by -2pc
}
\setlength\footnotesep{6.65\p@}
\setlength{\skip\footins}{9\p@ \@plus 4\p@ \@minus 2\p@}
\setlength\partopsep{2\p@ \@plus 1\p@ \@minus 1\p@}
\setlength{\leftmargini}{2em}
\setlength{\leftmarginii}{2.2em}
\setlength{\leftmarginiii}{1.87em}
\setlength{\leftmarginiv}{1.7em}
\setlength{\leftmarginv}{1em}
\setlength{\leftmarginvi}{1em}
\setlength{\labelsep}{.4em}
\setlength{\labelwidth}{\leftmargini}
\addtolength{\labelwidth}{-\labelsep}
\def\@listI{%
  \leftmargin \leftmargini
  \topsep  9\p@ \@plus 3\p@ \@minus 5\p@
  \partopsep 3\p@ \@plus 1\p@ \@minus 2\p@
  \itemsep 4.5\p@ \@plus 2\p@ \@minus 1\p@
  \parsep 4.5\p@ \@plus 2\p@ \@minus 1\p@ }
\def\@listii{%
  \leftmargin \leftmarginii
  \labelwidth \leftmarginii
  \advance\labelwidth by -\labelsep
  \topsep 4.5\p@ \@plus 2\p@ \@minus 1\p@
  \parsep 2\p@ \@plus 1\p@ \@minus 1\p@
  \itemsep \parsep}
\def\@listiii{%
  \leftmargin \leftmarginiii
  \labelwidth \leftmarginiii
  \advance\labelwidth by -\labelsep
  \topsep 2\p@ \@plus 1\p@ \@minus 1\p@
  \parsep \z@
  \partopsep 1\p@ \@plus 0\p@ \@minus 1\p@
  \itemsep \topsep}
\def\@listiv{%
  \setlength{\leftmargin}{\leftmarginiv}%
  \setlength{\labelwidth}{\leftmarginiv}%
  \addtolength{\labelwidth}{-\labelsep}}
\def\@listv{%
  \setlength{\leftmargin}{\leftmarginv}%
  \setlength{\labelwidth}{\leftmarginv}%
  \addtolength{\labelwidth}{-\labelsep}}
\def\@listvi{%
  \setlength{\leftmargin}{\leftmarginvi}%
  \setlength{\labelwidth}{\leftmarginvi}%
  \addtolength{\labelwidth}{-\labelsep}}
\let\@listi\@listI
\@listi
\setlength\floatsep{12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\textfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\intextsep{12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dblfloatsep{12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\@fptop{0\p@ \@plus 1fil}
\setlength\@fpsep{8\p@ \@plus 2fil}
\setlength\@fpbot{0\p@ \@plus 1fil}
\setlength\@dblfptop{0\p@ \@plus 1fil}
\setlength\@dblfpsep{8\p@ \@plus 2fil}
\setlength\@dblfpbot{0\p@ \@plus 1fil}
\def\labelenumi{\arabic{enumi}.}        % 1.
\def\theenumi{\arabic{enumi}}           % 1
\def\labelenumii{\alph{enumii})}        % a)
\def\theenumii{\alph{enumii}}           % a
\def\p@enumii{\theenumi}                % 1a
\def\labelenumiii{\it\roman{enumiii})}  % \it i)
\def\theenumiii{\roman{enumiii}}        % i
\def\p@enumiii{\theenumi(\theenumii)}   % 1(a)\it i)
\def\labelenumiv{\Alph{enumiv})}        % A)
\def\theenumiv{\Alph{enumiv}}           % A
\def\p@enumiv{\p@enumiii\theenumiii}    % 1(a)\it i)A
\def\labelitemi{\m@th$-$}
\def\labelitemii{\m@th$\bullet$}
\def\labelitemiii{\m@th$\ast$}
\def\labelitemiv{{\footnotesize +}}
\def\descriptionlabel#1{\hspace\labelsep \bf #1}
\newenvironment{description}{%
  \list{}{%
    \labelwidth\z@
    \itemindent -\leftmargin
    \let\makelabel\descriptionlabel
    }}{\endlist}
\newskip\topsepm@th
\if@kaplist
  \def\kapitemargs{%
   \topsep        \z@ \@plus 1pt
   \partopsep     \z@ \@plus 1pt
   \itemsep       \z@ \@plus \z@
   \parsep        \z@ \@plus 1pt
   \if@margspec \else \leftmargini   \z@ \fi
   \if@margspec \else \leftmarginii  1em \fi
   \if@margspec \else \leftmarginiii 1em \fi
   \if@margspec \else \leftmarginiv  1em \fi
   \if@margspec
     \leftmargin\csname leftmargin\romannumeral\@itemdepth\endcsname
     \labelwidth\leftmargin
     \advance\labelwidth-\labelsep
   \fi
   \rightmargin   \z@
   \listparindent \z@
   \itemindent    \z@
  }
  \def\kapenumargs{%
   \topsep        \z@ \@plus 1pt
   \partopsep     \z@ \@plus 1pt
   \itemsep       \z@ \@plus \z@
   \parsep        \z@ \@plus 1pt
   \if@margspec \else \leftmargini   \z@ \fi
   \if@margspec \else \leftmarginii  1em \fi
   \if@margspec \else \leftmarginiii 1em \fi
   \if@margspec \else \leftmarginiv  1em \fi
   \if@margspec
     \leftmargin\csname leftmargin\romannumeral\@enumdepth\endcsname
     \labelwidth\leftmargin
     \advance\labelwidth-\labelsep
   \fi
   \rightmargin   \z@
   \listparindent \z@
   \itemindent    \z@
  }
  \renewcommand{\@mklab}[1]{#1\hfil} % for custom list env-s only
\else
\def\kapenumargs{}
\def\kapitemargs{}
\fi
\def\@@enum@label#1{\hss \llap{#1}} % may stick out into l. margin
\def\@@item@label#1{\hss #1\hfil}
\def\enumerate{\@ifnextchar[%
    {\kap@enumerate}%
    {\if@margspec \kap@enumerate[] \else \kap@enumerate[00] \fi }}
\def\kap@enumerate[#1]{%
     \ifnum \@enumdepth >3 \@toodeep\else
       \advance\@enumdepth \@ne
       \edef\@enumctr{enum\romannumeral\the\@enumdepth}
       \list{\csname label\@enumctr\endcsname}{%
         \topsepm@th \topsep
         \kapenumargs
         \usecounter{\@enumctr}
         \settowidth\labelwidth{#1.}
         \setlength{\@tempdima}{\labelwidth}
         \addtolength{\@tempdima}{\labelsep}
         \if@margspec
           \ifdim \@tempdima > \leftmargin
             \setlength{\leftmargin}{\@tempdima}
           \fi
         \else
             \setlength{\leftmargin}{\@tempdima}
         \fi
         \let\makelabel\@@enum@label}
     \fi
   }
\let\endenumerate\endlist

\def\itemize{\@ifnextchar[{\kap@itemize}{\kap@itemize[]}}
\def\kap@itemize[#1]{\def\klu@arg{#1}%
    \ifnum \@itemdepth >3 \@toodeep
    \else
      \advance\@itemdepth \@ne
      \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
      \ifx \klu@arg\empty
        \list {\csname\@itemitem\endcsname}{%
        \topsepm@th \topsep
        \kapitemargs
          \let\makelabel\@@item@label}
      \else
        \list {\klu@arg }{%
          \kapitemargs
          \let\makelabel\@@item@label
          }
      \fi
    \fi
    }
\let\enditemize\endlist
\def\verse{\let\\=\@centercr
  \list{}{\itemsep\z@
      \itemindent -1.5em
      \listparindent \itemindent
      \rightmargin\leftmargin
      \advance\leftmargin 1.5em
  }\item[]}
\let\endverse\endlist

\def\quotation{\quoteskip
  \list{}{%
     \listparindent 1.5em
     \topsep .5ex plus 2pt minus 1pt
     \itemindent\listparindent
     \parsep 0pt plus 1pt
     }\item[]
  \hskip-\listparindent}
\def\endquotation{\endlist\quoteskip}

\def\quote{\quoteskip\list{}{%
  \leftmargin 1.5em
  \topsep .5ex plus 2pt minus 1pt
  }\item[]}
\def\endquote{\endlist\quoteskip}
\def\quoteskip{}

\def\frontmatter{\begingroup\thispagestyle{empty}%
    \renewcommand{\thepage}{\roman{page}}\setcounter{page}{1}}
\def\endfrontmatter{\newpage\endgroup\setcounter{page}{1}}
\newenvironment{notes}{\sectioncmd*{\notesname}\footnotesize
                    \begin{enumerate}}{\end{enumerate}%
                      \par \vskip 6pt \@plus 12pt \@minus 2pt}
\def\notesname{Notes}
\newenvironment{vitae}{%
    \begingroup
    \setcounter{enumiv}{0}%
    \global\setbox0=\vbox\bgroup
    }{%
    \egroup
    \ifnum \c@enumiv > 1
      \par\section*{\multiplevitaename}%
    \else
      \par\section*{\vitaename}%
    \fi
    \unvbox0 \endgroup \par
    \vspace{24pt}%
  }
\newcommand{\Vauthor}[1]{%
    \addtocounter{enumiv}{1}%
    \subsubsection*{#1}%
    }
  \def\vitaename{Author's Vitae}%
  \def\multiplevitaename{Authors' Vitae}%
\newbox\aobox
\newenvironment{ao}{%
  \global\setbox\aobox
  \vbox\bgroup
    \footnotesize\noindent
    \ifx\offprintsaddress\empty
    \leavevmode
    \else
      {\it \offprintsaddress:\/}\
    \fi
  }
  {\par\vskip18pt\egroup}
\newcommand{\make@ao}{%
    \@tempdima \ht\aobox
    \ifdim \@tempdima > 0pt
    \vskip 1pc % added by SK
    \par\noindent \unvbox\aobox
    \fi
    }
\newcommand{\offprintsaddress}{Address for Offprints}
\newenvironment{thenomenclature}{\section*{Nomenclature}
    \parbox[t]{.48\textwidth}\bgroup\parindent 0pt
    \footnotesize \begin{tabular}{p{2pc}p{11pc}}}{%
              \end{tabular}\egroup}
\newcommand{\splitnomen}{\end{tabular}\egroup~\parbox[t]{.48\textwidth}%
    \bgroup\parindent 0pt \footnotesize \begin{tabular}{p{2pc}p{11pc}}}
\newcommand{\nmc}[1]{\parbox[t]{11pc}{\raggedright #1}}
\def\verbatim@font{\normalsize\tt}
\def\acknowledgementsname{Acknowledgements}%
\def\acknowledgements{\section*{\acknowledgementsname}%
  \message{\acknowledgementsname}}
\def\endacknowledgements{\par \bigskip}
\gdef\title#1{\title@{#1}}
\gdef\author#1{\author@{#1}}
\gdef\date#1{\date@{#1}}
\gdef\nodagger@{%
  \def\@fnsymbol##1{\ensuremath{\ifcase##1\or *\or \ddagger\or
  \mathsection\or \mathparagraph\or \|\or **
  \or \ddagger\ddagger \else\@ctrerr\fi}}}
\def\opening{%
  \let\title=\title@
  \let\author=\author@
  \let\date=\date@
  \let\arttype=\arttype@
  \let\subtitle=\subtitle@
  \let\dedication=\dedication@
  \let\translation=\translation@
  \let\received=\received@
  \let\orf=\orf@
  \let\accepted=\accepted@
  \let\revised=\revised@
  \let\institute=\institute@
  \hsize\textwidth
  \let\nodagger\nodagger@
  }
\gdef\maketitle{\endopening}
\def\endopening{%
  \ifx\listfiles\@notprerr \maketitle@@ \else
  \AtBeginDocument{\maketitle@@}\fi
  \gdef\title##1{\opening@only\title}
  \gdef\subtitle##1{\opening@only\subtitle}
  \gdef\orf##1{\opening@only\orf}
  \gdef\dedication##1{\opening@only\dedication}
  \gdef\translation##1{\opening@only\translation}
  \gdef\received##1{\opening@only\received}
  \gdef\revised##1{\opening@only\revised}
  \gdef\author##1{\opening@only\author}
  \gdef\institute##1{\opening@only\institute}
  \gdef\date##1{\opening@only\date}%
  \gdef\arttype##1{\opening@only\arttype}
  \gdef\nodagger{\opening@only\nodagger}
  }
\def\opening@only#1{\PackageWarning{kluopen}{\string#1\space
                effective only inside opening environment.}}
\def\authorsize{\normalsize \raggedright}
\def\authorcase#1{#1}
\def\authorindent{0pt}
\def\afterallauthorsskip{1em\relax}
\def\afterauthorskip{0pt}
\def\institutesize{\footnotesize\it}
\def\institutecase#1{#1}
\def\instituteindent{0pt}
\def\institutesep{.4\baselineskip}
\def\authorand{and}
\def\i@oldseries{}
\newtoks\@temptokenb
\long\def\append@item#1\to#2{%
  \@temptokena={\@k@p{#1}}%
  \@temptokenb=\expandafter{#2}%
  \xdef#2{\the\@temptokenb\the\@temptokena}}
\def\get@left#1\to#2{\expandafter\g@l#1\g@l#1#2}
\long\def\g@l\@k@p#1#2\g@l#3#4{\def#4{#1}\def#3{#2}}
\def\@authors{}%
\def\@allauthors{}%
\def\@institutes{}%
\def\@instituteauthors{}%
\def\@curauths{}
\def\@curinst{}
\def\author@#1{\append@item#1\to\@authors
  \append@item#1\to\@allauthors }
\def\institute@#1{\append@item#1\to\@institutes
  \expandafter\append@item\expandafter{\@authors}\to\@instituteauthors
  \gdef\@authors{}}
\newif\ifthanks
\def\orf@#1{#1}
\def\@formatname#1#2{\begingroup
   \def\thanks##1{\global\thankstrue}\setbox0\vbox{#1}%
   \endgroup
   \begingroup
   \ifthanks
     \edef\fn##1\thanks##2{\authorcase{##1}\/%
        \noexpand\thanks{##2}#2}\expandafter\fn#1
   \else
      \edef\fn##1{{\authorcase{##1}}#2}%
        \expandafter\fn\expandafter{#1}%
   \fi
   \endgroup\global\thanksfalse }
\newcount\cnt@authors
\def\@formatauthors{\begingroup
  \authorsize
  \leavevmode
  \gdef\surname##1{##1}%
  \gdef\email##1{ \hbox{({\tt \lowercase{##1}})}}%
  \cnt@authors=0
  \def\@k@p##1{\advance\cnt@authors by 1}\@curauths
  \def\@k@p##1{\advance\cnt@authors by -1
    \ifnum\cnt@authors>1
    \@formatname{##1}{,}\penalty0\ \fi     % signif. space
    \ifnum\cnt@authors=1                               % before \fi's !!
    \@formatname{##1}{} \authorand \penalty0\ \fi
    \ifnum\cnt@authors<1
    \@formatname{##1}{}\par\fi}\@curauths
   \vskip \afterauthorskip
  \endgroup}
\def\@formatinstitute{{\institutesize \institutecase{\@curinst}\par}}
\newcount\cnt@institutes
\def\@authorsandinstitutes{\begingroup
  \authorsize
  \cnt@authors=0
  \def\@k@p##1{\advance\cnt@authors by 1}\@allauthors
  \cnt@institutes=0
  \def\@k@p##1{\advance\cnt@institutes by 1}\@institutes\relax
  \ifnum\cnt@institutes=0
    \let\@curauths\@allauthors
    \parindent=\authorindent
    \hangindent=\authorindent
    \@formatauthors
  \fi
  \loop\ifnum\cnt@institutes>0
    \get@left\@instituteauthors\to\@curauths
    \parindent=\authorindent
    \hangindent=\authorindent
    \@formatauthors
    \get@left\@institutes\to\@curinst
    \parindent=\instituteindent
    \hangindent=\instituteindent
    \@formatinstitute
    \ifnum\cnt@institutes>1 \vskip \institutesep\relax \fi
    \advance\cnt@institutes by -1
  \repeat
  \vskip \afterallauthorsskip
  \gdef\@authors{}%
  \gdef\@allauthors{}%
  \gdef\@institutes{}%
  \gdef\@instituteauthors{}%
  \gdef\@curauths{}%
  \gdef\@curinst{}%
\endgroup}
\def\titleflushstyle{}
\def\titlefont{\Large\rm}
\def\titlecase#1{#1}
\def\titleindent{0pt}
\def\aftertitleskip{1.8pc }
\def\presubtitleskip{-1.4pc }
\def\aftersubtitleskip{1pc }
\def\subtitlefont{\large\it}
\def\subtitleflushstyle{}
\def\title@#1{\gdef\@title{%
    \@formattitle{#1}\par \vskip \aftertitleskip }}
\def\@title{}
\def\@formattitle#1{\begingroup
  \def\thanks##1{\global\thankstrue}%
  \setbox\@tempboxa\vbox{#1}\endgroup
  \begingroup
    \titleflushstyle
    \ifthanks
      \def\fn##1\thanks##2{\ititle@{##1}{\,\thanks{##2}}}%
      \expandafter\fn#1
    \else
      \def\fn##1{\ititle@{##1}{}}\expandafter\fn\expandafter{#1}%
    \fi
  \endgroup\global\thanksfalse }
\def\titlebaselinefactor{1.05}
\def\ititle@#1#2{\begingroup
    \parindent \titleindent
    \hangindent \titleindent
    \hyphenpenalty10000
    {\titlefont\titlecase{#1}#2%
    \baselineskip=\titlebaselinefactor\baselineskip
    \par}
    \endgroup}
\def\@subtitle{}
\def\subtitle@#1{\gdef\@subtitle{\vskip \presubtitleskip
    \@formatsubtitle{#1}\par \vskip \aftersubtitleskip }}
\def\@formatsubtitle#1{\begingroup
  \def\thanks##1{\global\thankstrue}\setbox0\vbox{#1}\endgroup
  \begingroup \subtitleflushstyle
    \ifthanks
  \def\fn##1\thanks##2{\subtitle@thanks{##1}{##2}}\expandafter\fn#1
    \else
      \def\fn##1{\subtitle@@{##1}}\expandafter\fn\expandafter{#1}\fi
  \endgroup
  \par\global\thanksfalse}
\def\subtitle@thanks#1#2{\isubtitle@{#1}\thanks{#2}\par
    \ignorespaces}
\def\subtitle@@#1{\isubtitle@{#1}\par\ignorespaces}
\def\isubtitle@#1{{\subtitlefont #1}}
\def\afterdateskip{.7\baselineskip}
\def\datesize{\footnotesize}
\def\@date{{\i@oldseries\datesize Received: \@received ;
    Accepted\@accepted}\vskip \afterdateskip
    \gdef\@received{\ldots\ldots}%
    \gdef\@accepted{\ldots\ldots}}
\def\date@#1{\gdef\@date{{\i@oldseries\datesize #1\par}\vskip \afterdateskip
    \gdef\@received{\ldots\ldots}%
    \gdef\@accepted{\ldots\ldots}}}
\def\@received{\ldots\ldots}
\def\@accepted{: \ldots\ldots}
\def\revised@#1{\gdef\@accepted{ in revised form: #1}}
\def\received@#1{\gdef\@received{#1}}
\def\accepted@#1{\gdef\@accepted{ in final form: #1}}
\def\artsize{\normalsize\it}
\def\afterartskip{1.5pc}
\def\beforeartskip{0pc}
\def\@arttype{}
\def\arttype@#1{\gdef\@arttype{\vskip\beforeartskip\noindent
      {\artsize #1\vskip\afterartskip}}}
\def\@dedication{}
\def\dedicationsize{\normalsize\it\raggedright}
\def\prededicationskip{18pt}
\def\afterdedicationskip{18pt}
\def\dedication@#1{\gdef\@dedication{%
     \unskip\vskip \prededicationskip
     {\dedicationsize #1\par}%
     \vskip \afterdedicationskip}}
\def\@translation{}
\def\translationsize{\normalsize\it\raggedright}
\def\pretranslationskip{18pt}
\def\aftertranslationskip{18pt}
\def\translation@#1{\gdef\@translation{%
     \unskip\vskip \pretranslationskip
     {\translationsize #1\par}%
     \vskip \aftertranslationskip}}
\providecommand{\abstractname}{Abstract}
\providecommand{\keywordsname}{Keywords}
\providecommand{\abbreviationsname}{Abbreviations}
\providecommand{\nomenclaturename}{Nomenclature}
\def\abstractsize{\footnotesize}
\def\abstractnamefont{\bf}
\def\abstractdot{.~}
\def\keynamefont{\bf}
\def\nomennamefont{\bf}
\def\abbrevnamefont{\bf}
\def\classnamefont{\bf}
\def\afterabstractskip{.7\baselineskip\relax}
\def\preabstractskip{0pt\relax}
\newbox\@abstractbox
\def\@abstract{}
\newenvironment{abstract}{%
  \gdef\@abstract{\message{\abstractname}%
    {\vskip\preabstractskip
    \noindent
    \unvbox\@abstractbox
    \vskip\afterabstractskip }}%
  \global\setbox\@abstractbox\vbox\bgroup \abstractsize \noindent
    {\abstractnamefont\abstractname\abstractdot}}{\par\egroup }
\def\@keywords{}
\long\def\keywords#1{%
    \gdef\@keywords{\message{\keywordsname}%
        {\abstractsize\noindent{\keynamefont
      \keywordsname:~}#1\par \vskip.7\baselineskip}}}
\def\@abbreviations{}
\def\abbrev#1#2{#1 -- #2}
\long\def\abbreviations#1{%
     \gdef\@abbreviations{\message{\abbreviationsname}%
        {\abstractsize\noindent{\abbrevnamefont \abbreviationsname:~}%
        #1\par \vskip.7\baselineskip}}}
\def\@nomenclature{}
\def\nomen#1#2{#1 -- #2}
\long\def\nomenclature#1{%
     \gdef\@nomenclature{\message{\nomenclaturename}%
       {\abstractsize\noindent{\nomennamefont
       \nomenclaturename:\par}\noindent #1\par \vskip.7\baselineskip}}}
\def\@classification{}
\long\def\classification#1#2{%
     \gdef\@classification{\message{Classification}%
       {\abstractsize\noindent{\classnamefont #1: }%
       #2\par \vskip.7\baselineskip}}}
\def\motto{\@ifnextchar[{\prosemotto}{\poemmotto}}
\newbox\mottobox
\def\@motto{}
\long\def\poemmotto{\global\setbox\mottobox\vbox \bgroup
        \noindent
         \hbox to\hsize\bgroup\begingroup
            \hfill\vbox\bgroup\hsize =15pc
            \footnotesize \raggedright \noindent
            \parskip=3pt}
\long\def\prosemotto[#1]{\global\setbox\mottobox\vbox \bgroup
            \noindent
         \hbox to\hsize\bgroup \begingroup
            \hfill\vbox\bgroup\hsize =15pc
            \raggedright \footnotesize \noindent
            \parskip=3pt}
\def\endmotto{\par \egroup \endgroup \egroup
    \vspace{1\baselineskip}\egroup
    \gdef\@motto{\par\message{Motto}\box\mottobox \gdef\@motto{}}}
\def\@maketitle{%
   \@arttype \@title \@subtitle \@authorsandinstitutes \@date
   \@abstract \@keywords \@abbreviations \@classification
   \@nomenclature \@translation \@dedication \@motto}
\def\openingflushstyle{}
\def\maketitle@@{%
  \begingroup
     \setcounter{footnote}{0}%
     \def\thefootnote{\fnsymbol{footnote}}%
     \if@twocolumn
        \twocolumn[{\openingflushstyle
                 \parindent 0pt
                 \@maketitle}]
        \thispagestyle{opening}%
        \@extramaketitle
     \else
       \newpage\global\@topnum\z@
       \thispagestyle{opening}%
       {\openingflushstyle \parindent 0pt \@maketitle}%
     \fi
     \markboth{\@runningauthor}{\@runningtitle}%
     \@thanks
   \endgroup
   \setcounter{footnote}{0}%
   \let\@maketitle\relax
   \gdef\@thanks{}%
   \gdef\@title{}%
   \let\thanks\relax }
\def\runningtitle#1{\gdef\@runningtitle{#1}}
\gdef\@runningtitle{}
\def\runningauthor#1{\gdef\@runningauthor{#1}}
\gdef\@runningauthor{}
\long\def\journaldata#1#2\dataend{%
  \edef\@tempa{@#1}\ifx \@tempa\@currjournal #2\fi}
\def\CLsize{\footnotesize}
\def\@journal{}
\def\@currjournal{}
\def\journalcode#1{%
  \edef\@currjournal{@#1}%
  }
\def\i@oldseries{}
\newif\if@speccright \@speccrightfalse
\AtBeginDocument{\gdef\@speccrightcheck{%
   \if@speccright
   \footnotetext[4]{\@spectextone{} \@speccright{} \@spectexttwo}%
   \fi }}
\def\@spectextone{The}
\newcommand\spectextone[1]{\gdef\@spectextone{#1}}
\def\@spectexttwo{right to retain a non-exclusive, royalty free
                 licence in and to any copyright is acknowledged.}
\newcommand\spectexttwo[1]{\gdef\@spectexttwo{#1}}
\newcommand\copyrightowner{\@ifstar{\crightA}{\crightB}}
\newcommand\crightA[1]{\gdef\@speccright{#1}\global\@speccrighttrue}
\newcommand\crightB[1]{\gdef\@copyrightowner{#1}\global\@speccrightfalse}
\def\@speccright{}
\def\@copyrightowner{Kluwer Academic Publishers}
\newcommand\country[1]{\gdef\@country{#1}}
\def\@country{the Netherlands}
\newcommand\volume[1]{\gdef\@volume{#1}}
\def\@volume{00}
\newcommand\pubyear[1]{\gdef\@pubyear{#1}}
\def\@pubyear{\number\year}
\newif\iflastpagegiven   \lastpagegivenfalse
\newcommand\firstpage[1]{%
  \gdef\@firstpage{#1}%
  \ifnum\@firstpage>\c@page
    \setcounter{page}{#1}%
    \PackageWarning{kluopen}{Increasing pagenumber to \@firstpage}%
  \else \ifnum\@firstpage<\c@page
    \PackageWarning{kluopen}{Firstpage lower than pagenumber}\fi\fi
    \xdef\@firstpage{\the\c@page}%
    }
\def\@firstpage{1}
\def\pagenumbering#1{%
    \global\c@page \@ne
    \gdef\thepage{\csname @#1\endcsname \c@page}%
    \gdef\thefirstpage{%
            \csname @#1\endcsname \@firstpage}%
    \gdef\thelastpage{%
            \csname @#1\endcsname \@lastpage}%
    }
\pagenumbering{arabic}
\newcommand\lastpage[1]{\xdef\@lastpage{#1}%
  \global\lastpagegiventrue}
\def\@lastpage{0}
\def\setlastpage{\iflastpagegiven\else
    \edef\@tempa{@lastpage@\the\c@article}%
    \expandafter
    \ifx \csname \@tempa \endcsname \relax
        \gdef\@lastpage{0}%
    \else
        \xdef\@lastpage{\@nameuse{@lastpage@\the\c@article}}%
    \fi
    \fi }
\def\writelastpage{%
    \iflastpagegiven \else
    \immediate\write\@auxout%
    {\string\global\string\@namedef{@lastpage@\the\c@article}{\the\c@page}}%
    \fi
    }
\def\thepagerange{%
  \ifnum\@lastpage =0 {\ \bf PLEASE RUN AGAIN} \else
  \ifnum\@lastpage = \@firstpage \ \thefirstpage\else
  \ \thefirstpage--\thelastpage \fi\fi}
\def\@prin{Printed in}
\@ifundefined{textcopyright}{\def\textcopyright{\copyright}}{}
\def\copyrightline{\textcopyright~\i@oldseries\@pubyear\
  {\it\@copyrightowner.~~\@prin\ \@country.}\hfill\hbox{}}
\def\volsep{: }
\def\thejournal{\ifx\@journal\empty\else\leavevmode \i@oldseries
     {\it\@journal\/}~~{\bf\i@oldseries\@volume\volsep}\thepagerange,
     \@pubyear.\hfill\hbox{}\\ \fi}
\def\no{no}
\def\crline#1{\gdef\@crline{#1}}
\def\thecopyright{\ifx\@crline\no \else \copyrightline \par \fi }
\newtoks\logotoks
\catcode`\%=12
\catcode`\#=12
\logotoks={\special{"
4 4 translate
989 1138 1 [60 0 0 -60 210 930]
currentfile
/ASCII85Decode filter
<< /K -1 /Columns 989 >>
/CCITTFaxDecode filter
image
Q>'H49/K0rjdMhW-(A!cb;A.`/DC9EH"NLrmTGB3G`p9Q"2Q+cbR4Nj7'd7dn1Os5
\string$DPm^#D5dp.Sq0)HOI.%W!@rm_0-3j?%po`_0-3j?%VDq_0-W'Fr+S1(LXi_Ye(:I
]*kjT\string$a@6KL"blG_X2L_CTtEVL"blG_X2L_CTtEVY/9RL]*l%#ln6muG.V%6g?j&"
CUMm`Fr+r%g?j'q?%q#"G.V%_f3rj7?*;dp[G("lm<6*IY1IHshmM2*G.V%_f7)=e
[G("lm<6*Iqd\string$AVIb/AMCUMmbg?j'qp:FV5rN=b\string$f7)=e^MCT"[GSCL[G(*'m<@rA
m<6,8\string\:3%Yf7)>#f7)>#f7)>#f7)>#f7)>#f7)>#f7)>#f7)>#rN?+r?2Iq)p:L(d
GOO8ShmM@LhnNsAIb0&IY5S7k]D(dJn)(P1^OFd`rVKmtp:L(fg@*q6CVP>sqd'*n
n)(lq^OH.Yp[*1nhnOWlIf90<n(R6f^OH.Yp[@"SCVP>sqtKR:^OH.Yp[@"SCVP>s
qtKQ8s8U1@C);u92\string$r0TIf90<e+`=g^OH.YpZ,==\string\+]gYg\string\ZD'qgWPOrP,i8rnlK-
IrF`IDsdM<\string\+]gY<rV"2qgWPOol'6r^UNq9hcBa6g\string\ZJ=mIbDbrP,i8qR?1thqRGR
g\string\ZJ=X+,'TrP#E4^UNq5\string\+]gYgZYS:s0qsA>CC\string\p\string\,F'GI<PY"lYir`pAJk\string$g]\string$*4
^:SmLos`Okqg[AbD?"OWhlXZ\string\p"T/KrP"TTpAJk\string$g]\string$*4^:Sj&s0pTuf&'cJ>CC\string\n
D=uZ_hb.nbI4`5\string$oX=e/f5K6t?,'TlG5Z:Ng\string\&&-Dq<fO^KZ,0qHJI(l#\string$H=V75&p
f&'cIQJ_E4>CYDlD=uZV\string\(>QLhd*s^hlchCoX=e/dbFH(f5ILprP"TT?+uW^XhMDq
/\string\\iG[ea3VG5>El[ea3VG5>El[ea3VG5>El[efC`[ea3V/\string\\iF/\string\[P.XhMDq/\string\[P.
95gZ9f5ILpdbF#'oX=U#J(s4)oX=U#I4`1!hb.mjhb.ma\string\'j\string$qD=k:5>CA*;QJW!c
oX=U#I4`1FI4`1!hb.ma\string\'j\string$qD=EkK95gZ9_HVF?^(T2bD=eV\string$$#T=CqHJ=n\string\'j\string$i
/\string\[P.95fJ!hb.m@[eNL6V74;LDl'q[>C7R%qHJ=i[eNL6V74;LDl'q[\string$ZC^,qHJ=Y
>C7a+_@(:8[eN.*n:KEQQJVs"^(T2Z"h2?QHm#lm6#H*aDh8@8Jm3UF[eLuRp`R\string$?
6#H*WD=C2:KGNGN/\string\XRt27@;0aCL\string$khf"Uu#*%Ks"Le+7OAWdIj>'(dl*n`EL,P%*
&6jO::U(jdL-R<W?Jcof\string$<nG'j>\string$a;@XEKW5W@E:h]\string\'fZTZ&2IlgdAO<XZ3Ig*T=
hna6h\string\+!b`J";.F81K*N-5drJr9P82JLC&riK=?dcL_O,/H-%Tm_N_SP<`=[r2g%Q
1&S&'fJid;r.0IP.XrTBC_ZpLs8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!
s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!
s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!s8W-!r-X"n
rVQ?XhnG_tIf90<n)(m/rVQ?XhnG_tIf90<n)(m/rUg'cp[@!8hnOX=o_n[]n)\string$pu
^OH.RrVQ?XhbW.EIenNlqs""Pn#,X3^7W/hqL8D?l215DVsiNWT>,jOIenNlo_n[O
qs""Pe+_>cn#,WPn)\string$pu^7W-3^O8=p5CGbE5CGbE5CGbE5CGcgrUg'\string\rUg'\string\qL89h
5CG_f^7S3Y:Z"sGn#+Y/e*6boo_nFYI6W-DT22BRVpjo-l1Fh#5CG_f:T*ZZe*6N\string$
I6O9!Vpjo&qL(Q":T)\string\+o_Nu"T21.:I6O9!K_g*\string\T21.:I6O9!K_g*\string\'C#/a:T)'X
5+`/RpeRg)I6O80o_;48peQS>HmcdY-e%\string$<'B)+gl0qK%pa<q+-c%t[i1C>FT*b&n
L=7gF:P*s-i1C/I-c%t[j:;B)"QU(.PuEc.AeiBCZN4SP=c/;D"]f?=L:]C?)O[;?
Ai"3B!'gY\string~>
}}
\catcode`\%=14
\catcode`\#=6
\def\kaplogo{\advance\textwidth -2pc
    \leavevmode\lower 8pt
    \hbox to 24pt{\the\logotoks\hss}}
\if@copyrighthead
  \gdef\@copyrighthead{{\parindent 0pt\vbox to\headheight {%
          \hsize\textwidth \vss \kaplogo
          \parbox{\textwidth}{\CLsize\thejournal\thecopyright}}}}
  \gdef\@copyrightfoot{}
\else
  \gdef\@copyrightfoot{{\parindent 0pt\rlap{\vbox to 0pt{%
          \hsize\textwidth \vss \kaplogo
    \parbox{\textwidth}{\CLsize\thejournal\thecopyright}\vss}}}}
  \gdef\@copyrighthead{}
\fi
\def\@kapidenthead{}
\def\@kapidentfoot{}
\if@kapidenthead
  \def\editor#1{\gdef\@kapidentfoot{}%
    \if@noid \gdef\@kapidenthead{}\else
    \gdef\@kapidenthead{\footnotesize \tt #1 (\klujnlname:\kluclassname)\ v.%
        \kluclassversion\hfill}\fi}
\else
   \def\editor#1{\gdef\@kapidenthead{}%
     \if@noid \gdef\@kapidentfoot{}\else
     \gdef\@kapidentfoot{\vbox to 0pt{%
       \rlap{\vbox to \id@boxheight{\hbox{}\vfill
             \hbox to \textwidth{\footnotesize\tt\hbox{}\hfill #1
             (\klujnlname:\kluclassname)\ v.\kluclassversion}%
               \vskip 10pt}}\vss}}\fi}
\fi
\newcounter{outputpage}
\def\idline{\if@noid\else
    \stepcounter{outputpage}%
    \rlap{\smash{\vtop to \id@boxheight{%
     \vfil\hbox to\textwidth{%
     \hfil\footnotesize\tt
     \jobname.tex; \TODAY;~\timenow;~p.\theoutputpage}}}}%
   \fi}
\DeclareTextAccent{\@acci}{OT1}{19}
\DeclareTextAccent{\@accii}{OT1}{18}
\DeclareTextAccent{\@acciii}{OT1}{22}
\DeclareTextAccent{\@acci}{T1}{1}
\DeclareTextAccent{\@accii}{T1}{0}
\DeclareTextAccent{\@acciii}{T1}{9}
\gdef\markboth#1#2{{\let\protect=\noexpand
    \xdef\myleftmark{\Uppercase{#1}}%
    \xdef\myrightmark{\Uppercase{#2}}}}
\let\imarkboth\markboth
\def\myleftmark{}
\def\myrightmark{}
\def\@markfont{\rm\scriptsize}
\def\@pgnumfont{\rm\normalsize}
\def\ps@headings{%
  \def\@oddfoot{\idline\hfil }%
  \let\@evenfoot\@oddfoot
  \def\@evenhead{\hbox{}\@pgnumfont\rlap{\thepage}\hfil
    \@markfont\myleftmark\hfil}%
  \def\@oddhead{\hbox{}\hfil\@markfont\myrightmark\hfil
    \@pgnumfont\llap{\thepage}}%
  \let\@mkboth\@gobbletwo
  \def\chaptermark##1{}%
  \def\sectionmark##1{}%
  \def\subsectionmark##1{}}
\def\ps@myheadings{%
  \def\@oddfoot{\idline\hfil }%
  \let\@evenfoot\@oddfoot
  \def\@evenhead{\hbox{}\@pgnumfont\rlap{\thepage}\hfill
    \@markfont\myleftmark}%
  \def\@oddhead{\hbox{}\@markfont\myrightmark\hfill
    \@pgnumfont\llap{\thepage}}%
  \let\@mkboth\@gobbletwo
  \def\chaptermark##1{}%
  \def\sectionmark##1{}%
  \def\subsectionmark##1{}}
\def\ps@empty{%
  \def\@oddfoot{\idline\hfil }%
  \let\@evenfoot\@oddfoot
  \def\@evenhead{}%
  \def\@oddhead{}%
  \let\@mkboth\@gobbletwo
  \def\chaptermark##1{}%
  \def\sectionmark##1{}%
  \def\subsectionmark##1{}}
\let\ps@title\ps@empty
\let\ps@part\ps@empty
\let\ps@chapter\ps@empty
\def\ps@monoheadings{%
    \let\@mkboth\@gobbletwo
    \def\@oddfoot{\idline\hfil}%
    \let\@evenfoot\@oddfoot
    \def\@evenhead{\hbox{}\rm\normalsize\hbox to 0pt{\thepage\hss}\hfil
         \footnotesize\myleftmark\hfil}%
    \def\@oddhead{\hbox{}\rm\footnotesize\hfil
        \myrightmark\hfil
        \rm\normalsize\hbox to 0pt{\hss\thepage}}%
    \def\chaptermark##1{%
        \if@mainmatter
        \markboth{\@chapapp\ \NUMTOWORD{\c@chapter}}{\@runningtitle}%
        \else
        \markboth{\@chapapp\ \thechapter}{\@runningtitle}%
        \fi }
    \let\sectionmark\@gobble
  }
  \def\ps@monotitle{\let\@mkboth\@gobbletwo
    \def\@oddhead{\hbox{}\rm\footnotesize\hfil
         \myleftmark\hfil}%
    \def\@oddfoot{\idline \@barcode\@kapidentfoot
        \parbox{\textwidth}{\hfil\thepage\hfil\\ \@copyrightfoot}}
    \let\@evenhead\@oddhead
    \let\@evenfoot\@oddfoot
    \let\chaptermark\@gobbletwo
    \let\sectionmark\@gobble
    \let\subsectionmark\@gobble
  }
  \def\ps@monochapter{\let\@mkboth\@gobbletwo
    \def\@oddhead{\hbox{}\hfil\rm\footnotesize
        \myleftmark\hfil}%
    \def\@oddfoot{\idline\hfil\rm\normalsize\thepage\hfil}%
    \let\@evenhead\@oddhead
    \let\@evenfoot\@oddfoot
    \let\chaptermark\@gobbletwo
    \let\sectionmark\@gobble
    \let\subsectionmark\@gobble
  }
  \def\ps@editheadings{\let\@mkboth\@gobbletwo
    \def\@oddfoot{\idline\hfil}%
    \def\@evenfoot{\idline\hfil}%
    \def\@evenhead{\hbox{}\rm\normalsize\rlap{\thepage}\hfil
         \footnotesize\myleftmark\hfil}%
    \def\@oddhead{\hbox{}\rm\footnotesize\hfil\myrightmark\hfil
        \rm\normalsize\hbox to 0pt{\hss\thepage}}%
    \def\chaptermark##1{%
        \markboth{\@runningauthor}{\@runningtitle}}%
    \let\sectionmark\@gobble
  }
  \def\ps@edittitle{\let\@mkboth\@gobbletwo
    \def\@oddhead{\hbox{}\rm\footnotesize\hfil
         \myleftmark\hfil}%
    \def\@oddfoot{\idline \@barcode\@kapidentfoot
        \parbox{\textwidth}{\hfil\raise 6pt\hbox{\thepage}\hfil\\ \@copyrightfoot}}
    \let\@evenhead\@oddhead
    \let\@evenfoot\@oddfoot}
\def\theinheadpage{\thepage}
\def\ps@opening{%
  \def\@oddhead{\@copyrighthead \@kapidenthead\hss
            \if@copyrighthead \llap{\theinheadpage}\fi }%
  \let\@evenhead\@oddhead
  \def\@oddfoot{\@copyrightfoot \@barcode\idline\@kapidentfoot\hss}
  \let\@evenfoot\@oddfoot}
\newcounter{article}
\renewcommand{\thearticle}{}
\let\ilabel=\label
\let\iref=\ref
\let\ipageref=\pageref
\let\art@intdefinecounter\@definecounter
\newif\ifinarticle % \inarticlefalse
\newenvironment{article}{%
  \def\@definecounter##1{\art@intdefinecounter{##1}%
    \@addtoreset{##1}{article}}%
  \renewcommand{\thearticle}{\roman{article}}%
  \refstepcounter{article}%
  \message{Article \number\c@article}%
  \gdef\@firstpage{\the\c@page}%
  \@addtoreset{equation}{article}%
  \ifx\sectioncmd\section
    \@addtoreset{section}{article}%
  \else
    \@addtoreset{chapter}{article}%
  \fi
  \@addtoreset{endnote}{article}%
  \@addtoreset{table}{article}%
  \@addtoreset{figure}{article}%
  \@addtoreset{algorithm}{article}%
  \def\label##1{\ilabel{\thearticle ##1}}%
  \def\ref##1{\iref{\thearticle ##1}}%
  \def\pageref##1{\ipageref{\thearticle ##1}}%
  \setlastpage
  \global\inarticletrue
  }{\make@ao
    \writelastpage
    \clearpage
    \if@openright
      \ifodd \c@page \else ~\thispagestyle{empty}\newpage \fi
    \fi
    \gdef\@dedication{}\gdef\@translation{}%
    \gdef\@title{}\gdef\@subtitle{}%
    \gdef\@arttype{}\gdef\@keywords{}\gdef\@classification{}%
    \gdef\@nomenclature{}\gdef\@abbreviations{}\gdef\@abstract{}%
    \gdef\@kapidenthead{}\gdef\@kapidentfoot{}%
    \gdef\@barcode{}\gdef\@firstpage{\thepage}%
    \gdef\@crline{}%
    \global\lastpagegivenfalse
    \global\inarticlefalse
    }
\AtBeginDocument{\setlastpage}
\AtEndDocument{\ifnum \c@article=0
    \writelastpage
    \clearpage\fi}
\font\barcodefont=cmr10
\def\barcode#1{\global\font\barcodefont=barcodes
  \gdef\@barcode{\rlap{\vbox to 0pt{%
      \vbox to \id@boxheight{\hbox{}\vfill
           {\barcodefont \hbox{#1}}}\vss}}}}
\def\@barcode{}
\def\PIPSID#1{}
\parskip 0pt
\hyphenpenalty 200
\doublehyphendemerits 640000  % corresponds to badness 800
\finalhyphendemerits  1000000  % corresponds to badness 1000
\arraycolsep 6pt
\tabcolsep 6pt
\arrayrulewidth .4pt
\doublerulesep 2pt
\def\@rcline[#1-#2]{%
  \noalign{%
       \global\@cla #1\relax
       \global\advance\@cla\m@ne
       \ifnum\@cla >0
         \global\let\@tabklu@tmpa\@rclinea
       \else
         \global\let\@tabklu@tmpa\@rclineb
       \fi
       \global\@clb #2\relax
       \global\advance\@clb-\@cla }%
    \@tabklu@tmpa
    \noalign{\vskip-\arrayrulewidth}%
  }%
\def\@rclinea{%
    \multispan\@cla&\multispan\@clb
    \hbox to 3pt{\hfil }%
    \unskip
    \leaders\hrule \@height \arrayrulewidth\hfill
    \cr}%
\def\@rclineb{%
   \multispan\@clb
   \hbox to 3pt{\hfil }%
   \unskip
   \leaders\hrule \@height \arrayrulewidth\hfill
   \cr}%
\def\@lcline[#1-#2]{%
  \noalign{%
     \global\@cla #1\relax
     \global\advance\@cla\m@ne
     \ifnum\@cla >0
        \global\let\@tabklu@tmpa\@lclinea
     \else
        \global\let\@tabklu@tmpa\@lclineb
     \fi
     \global\@clb #2\relax
     \global\advance\@clb-\@cla
  }\@tabklu@tmpa
  \noalign{\vskip-\arrayrulewidth}%
}%
\def\@lclinea{%
     \multispan\@cla&\multispan\@clb
     \unskip
     \leaders\hrule \@height \arrayrulewidth\hfill
     \hbox to 3pt{\hfil }\cr}%
\def\@lclineb{%
     \multispan\@clb
     \unskip
     \leaders\hrule \@height \arrayrulewidth\hfill
     \hbox to 3pt{\hfil }\cr}%
\def\@lrcline[#1-#2]{%
   \noalign{%
     \global\@cla #1\relax
     \global\advance\@cla\m@ne
     \ifnum\@cla>0
        \global \let\@tabklu@tmpa\@lrclinea
     \else
        \global \let\@tabklu@tmpa\@lrclineb
     \fi
     \global \@clb #2\relax
     \global \advance\@clb-\@cla
     }%
     \@tabklu@tmpa
     \noalign{\vskip -\arrayrulewidth}%
  }%
\def\@lrclinea{%
     \multispan\@cla&\multispan\@clb
     \hbox to 3pt{\hfil }%
     \unskip\leaders\hrule \@height \arrayrulewidth\hfill
     \hbox to 3pt{\hfil }%
     \cr}%
\def\@lrclineb{%
     \multispan\@clb
     \hbox to 3pt{\hfil }%
     \unskip\leaders\hrule \@height \arrayrulewidth\hfill
     \hbox to 3pt{\hfil }%
     \cr}%
\newlength\stretchtabsep
\setlength\stretchtabsep{0pt plus 1fil}
\AtBeginDocument{%
\let\savehline\hline
\def\tabular{\begingroup
   \def\hline{\noalign{\vskip3pt}\savehline\noalign{\vskip3pt}}%
   \def\rcline##1{\@rcline[##1]}%
   \def\lcline##1{\@lcline[##1]}%
   \def\lrcline##1{\@lrcline[##1]}%
   \let\rlcline=\lrcline
    \setbox\strutbox\hbox{\vrule height.8\baselineskip
            depth.4\baselineskip width\z@}%
    \setbox0=\hbox\bgroup\def\@halignto{}\@tabular}%
\def\endtabular{\crcr\egroup\egroup $\egroup
  \egroup \tabwidth{\wd0}\unhbox0 \endgroup}%
\let\klu@intarray\array
\let\klu@intendarray\endarray
\def\array{\begingroup \let\hline\savehline \klu@intarray }
\def\endarray{\klu@intendarray \endgroup}
\@ifundefined{newcolumntype}{% array.sty not loaded
\@namedef{tabular*}#1{%
   \begingroup
   \let\savehline\hline
   \def\hline{\noalign{\vskip3pt}\savehline\noalign{\vskip3pt}}%
   \def\rcline##1{\@rcline[##1]}%
   \def\lcline##1{\@lcline[##1]}%
   \def\lrcline##1{\@lrcline[##1]}%
   \let\rlcline=\lrcline
     \setbox\strutbox\hbox{\vrule height.8\baselineskip
            depth.4\baselineskip width\z@}%
      \setbox0=\hbox\bgroup\def\@halignto{to #1}%
        \def\@tabacol{\edef\@preamble{\@preamble
            \tabskip \stretchtabsep \hskip \tabcolsep}}\@tabular}%
}{% array.sty loaded:
\@namedef{tabular*}#1{%
   \begingroup
   \let\savehline\hline
   \def\hline{\noalign{\vskip3pt}\savehline\noalign{\vskip3pt}}%
   \def\rcline##1{\@rcline[##1]}%
   \def\lcline##1{\@lcline[##1]}%
   \def\lrcline##1{\@lrcline[##1]}%
   \let\rlcline=\lrcline
     \setbox\strutbox\hbox{\vrule height.8\baselineskip
            depth.4\baselineskip width\z@}%
      \setbox0=\hbox\bgroup
      \gdef\@halignto{to #1}%
        \@tabular}%
} % end array.sty loaded
\@namedef{endtabular*}{\endtabular}
\def\TABULAR{%
     \let\savehline\hline %compatibility
     \let\rcline\cline \let\lcline\cline
     \let\lrcline\cline \let\rlcline\cline
     \setbox0=\hbox\bgroup\def\@halignto{}\@tabular}%
\def\endTABULAR{\crcr\egroup\egroup $\egroup
  \egroup \tabwidth{\wd0}\unhbox0 }%
\@namedef{TABULAR*}#1{%
     \let\savehline\hline %compatibility
     \let\rcline\cline \let\lcline\cline
     \let\lrcline\cline \let\rlcline\cline
     \setbox0=\hbox\bgroup\def\@halignto{to #1}\@tabular}%
\@namedef{endTABULAR*}{\endtabular}} % end of AtBeginDocument
\setcounter{topnumber}{2}
\setcounter{bottomnumber}{1}
\setcounter{totalnumber}{3}
\setcounter{dbltopnumber}{2}
\renewcommand{\topfraction}{.85}
\renewcommand{\textfraction}{.01}
\renewcommand{\bottomfraction}{.4}
\renewcommand{\floatpagefraction}{.84}
\renewcommand{\dblfloatpagefraction}{.84}
\renewcommand{\dbltopfraction}{.7}
\def\figtabdot{.}
\def\tablename{Table}%
\def\figurename{Figure}%
\def\algorithmname{Algorithm}%
\newdimen\maxfloatwidth
\newbox\figtabbox
\newdimen\floatindent
\newdimen\@tabskip
\gdef\cap@type{0}
\newdimen\captionskip
\setlength\captionskip{6pt}
\newdimen\@tabwidth
\setlength\@tabwidth{\textwidth}
\def\tabwidth#1{\global\setlength\@tabwidth{#1}}
\def\@getmaxwidth{\maxfloatwidth=\hsize
    \if@kaprotate \maxfloatwidth=\textheight \fi }
\def\@floatcorrect{\if@kaprotate\else
  \advance\maxfloatwidth -\floatindent \fi }
\def\hbox@to@floatwidth#1{\leavevmode
        \hbox to \@tabwidth{#1}}
\def\@getindent{%
   \ifnum\cap@type=2 \else
        \@tabwidth=\if@kaprotate \textheight \else \hsize \fi
        \if@figindent\advance \@tabwidth -\floatindent \fi\fi
   \ifnum\cap@type=1
     \if@figindent \@tabskip\floatindent
       \else \@centeredfloat \fi
   \else \ifnum\cap@type=2
            \if@tabindent \@tabskip\floatindent
               \else \@centeredfloat  \fi
            \ifdim \@tabwidth > \maxfloatwidth
                \@tabskip 0pt
                \floatindent 0pt
            \fi
         \else
            \@centeredfloat
         \fi
   \fi
}
\def\@centeredfloat{%
     \floatindent\maxfloatwidth
     \advance\floatindent by -\@tabwidth
     \divide\floatindent by 2
     \@tabskip\floatindent
     \if@kaprotate
       \@tabskip\hsize
       \advance\@tabskip by -\ht\figtabbox
       \advance\@tabskip by -\dp\figtabbox
       \divide\@tabskip by 2
     \fi
}
\newif\if@centeredfigcaption
\newif\if@centeredtabcaption
\@centeredtabcaptiontrue
\@centeredfigcaptiontrue
\def\indentedtabcaptions{\global\@centeredtabcaptionfalse }
\def\indentedfigcaptions{\global\@centeredfigcaptionfalse }
\def\indentedcaptions{\global\@centeredtabcaptionfalse
    \global\@centeredfigcaptionfalse}
\newdimen\captionindent
\setlength\captionindent{0pt}
\newtoks\@floatcaption
\def\tabcapspace{.5em}
\def\tabcapfont{\footnotesize }
\long\def\@maketabcaption#1#2{\global\@floatcaption={#2}%
   \message{\tablename\space\thetable \if@kaprotate
     \space(rotated) \fi}}
\def\@klu@caption{%
  \setbox1=\hbox{\tabcapfont\fnum@table\hskip\tabcapspace
    \the\@floatcaption}%
  \noindent
  \ifdim\wd1 >\@tabwidth
     {\if@centeredtabcaption\centering\else \hskip \captionindent\fi
     \parbox[b]{\@tabwidth}{\tabcapfont\unhbox1}}%
  \else
     \hbox to \@tabwidth{%
       \if@centeredtabcaption \hfil \else \hskip \captionindent\fi
       \tabcapfont\fnum@table
       \hskip\tabcapspace{\tabcapfont\the\@floatcaption}\hfil }%
  \fi
  \if@kaprotate \else \par \vskip -\baselineskip \fi
  \par
}
\def\@klu@figcaption{%
  \setbox1=\hbox{\figcapfont\fnum@figure\hskip\tabcapspace
            \the\@floatcaption}%
  \noindent
  \ifdim\wd1 >\@tabwidth
     {\if@centeredfigcaption\centering\else \hskip \captionindent\fi
     \parbox{\@tabwidth}{\figcapfont\unhbox1}}%
  \else
     \hbox to \@tabwidth{%
       \if@centeredfigcaption \hfil\else \hskip \captionindent\fi
       \tabcapfont\fnum@figure
       \hskip\tabcapspace{\figcapfont\the\@floatcaption}\hfil}%
  \fi
  \par
}
\def\splitcaptions{\splittabcaptions\splitfigcaptions}
\def\splittabcaptions{
  \def\@klu@caption{%
    \setbox1=\hbox{\tabcapfont\the\@floatcaption}%
    \noindent
    \ifdim\wd1 >\@tabwidth
     \hbox to \@tabwidth{\if@centeredtabcaption\hss\else
       \hskip\captionindent\fi
     \tabcapfont\fnum@table\hss}\vskip \tabcapspace
       \vskip 6pt
     {\if@centeredtabcaption\centering\fi
       \hskip \captionindent
          \parbox{\@tabwidth}{\tabcapfont\unhbox1}}%
   \else
     \hbox to \@tabwidth{%
       \if@centeredtabcaption \hfil\else \hskip\captionindent\fi
       \tabcapfont\fnum@table\strut\hfil }\vskip \tabcapspace
      \hbox to \@tabwidth{%
       \if@centeredtabcaption \hfil\else \hskip\captionindent \fi
       \tabcapfont\the\@floatcaption \hfil }%
       \if@kaprotate \else \par \vskip -\baselineskip \fi
   \fi
   \par
}}
\def\splitfigcaptions{\def\@klu@figcaption{%
    \setbox1=\hbox{\figcapfont\the\@floatcaption}%
    \noindent
    \ifdim\wd1 >\@tabwidth
     \hbox to \@tabwidth{\if@centeredfigcaption\hfil\else
       \hskip\captionindent\fi
            \figcapfont\fnum@figure\hfil}\vskip \tabcapspace
       \vskip 6pt
     {\if@centeredfigcaption\centering\fi \hskip \captionindent
            \parbox{\@tabwidth}{\figcapfont\unhbox1}}%
   \else
     \hbox to \@tabwidth{%
       \if@centeredfigcaption \hfil\else \hskip\captionindent\fi
       \figcapfont\fnum@figure\strut\hfil }\vskip \tabcapspace
      \hbox to \@tabwidth{%
       \if@centeredfigcaption \hfil\else \hskip\captionindent\fi
       \figcapfont\the\@floatcaption \hfil }%
   \fi
   \par
}}%
\@ifundefined{thetable}{\newcounter{table}}{}
\def\thetable{\arabic{table}}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename~\thetable\figtabdot}
\newif\if@tabindent \@tabindentfalse
\def\tableindent#1{%
   \global\floatindent= #1\global\@tabindenttrue }
\def\tabfont{\footnotesize}
\def\@tabnotes{}
\newcounter{tabnote}
\def\tabnotemark{\ensuremath{^{\thetabnote}}}
\def\thetabnote{\arabic{tabnote}}
\def\tabnotesep{\par}
\def\tabnote#1{\stepcounter{tabnote}%
    \rlap{\tabnotemark }%
    \begingroup
    \let\tabnotesep\relax
    \xdef\@tabnotes{\@tabnotes\tabnotesep \tabnotemark #1\par}%
    \endgroup }
\long\def\tabnotes#1{\gdef\@tabnotes{{\tabfont\noindent #1\par}}}
\def\@setnotrotatedtabbox{%
  \setbox4=\hbox to \maxfloatwidth{\vbox{\hsize=\maxfloatwidth
     \@klu@caption
     \vskip\captionskip \leavevmode
     \unvbox\figtabbox\par
     \noindent\parbox{\@tabwidth}{\tabfont\@tabnotes}\par}}%
      \if@fixedfloat\calc@fixedspace4\fi
  \noindent\kern \floatindent\box4
 }
\def\@setrotatedtabbox{\begingroup \hfuzz=\vsize
     \setbox2\hbox to \textheight{\hfil
        \vbox to \hsize{\hsize=\vsize
         \vfil
         \hbox{\hbox@to@floatwidth{\vbox{\@klu@caption }}}
         \vskip\captionskip
         \hbox{\hbox@to@floatwidth{\box\figtabbox\hss}}%
         \hbox{\hbox@to@floatwidth{\parbox{\@tabwidth}{\tabfont\@tabnotes}\hfil }}%
         \vss
    }\hss}\rotl{2}\endgroup
}
\def\table{\let\@makecaption\@maketabcaption
    \global\@floatcaption={}%
    \gdef\@tabnotes{}\setcounter{tabnote}{0}\gdef\cap@type{2}%
    \@ifnextchar[{\t@blewithoptions}{\t@blewithoptions[tbp]}}
\def\t@blewithoptions[#1]{%
    \if H#1\@fixedtable \else \@float{table}[#1]\fi
    \@getmaxwidth \if@tabindent \@floatcorrect \fi
    \setbox\figtabbox\vbox\bgroup\tabfont
    \if@kaprotate\hfuzz=\vsize\fi }%
\def\endtable{\egroup \@getindent
  \gdef\cap@type{0}\noindent
  \hfuzz=\floatindent
    \if@kaprotate \@setrotatedtabbox
    \else \@setnotrotatedtabbox \fi
  \if@fixedfloat \vskip\intextsep \@fixedfloatfalse
  \else \end@float \fi
  \hfuzz =0.1pt }%
\@namedef{table*}{\let\@makecaption\@maketabcaption
    \global\@floatcaption={}%
    \gdef\@tabnotes{}\setcounter{tabnote}{0}\gdef\cap@type{2}%
    \@ifnextchar[{\dt@blewithoptions}{\dt@blewithoptions[tbp]}}
\def\dt@blewithoptions[#1]{%
    \if H#1\if@twocolumn \@dblfloat{table}[t]\else \@fixedtable\fi
    \else \@dblfloat{table}[#1]\fi
    \@getmaxwidth \if@tabindent \@floatcorrect \fi
    \setbox\figtabbox\vbox\bgroup\tabfont
    \if@kaprotate \hfuzz=\vsize \fi }%
\@namedef{endtable*}{\egroup  \@getindent
    \gdef\cap@type{0}\noindent
    \hfuzz=\floatindent
    \if@kaprotate \@setrotatedtabbox
    \else \@setnotrotatedtabbox \fi
    \if@fixedfloat  \vskip\intextsep \@fixedfloatfalse
    \else \end@dblfloat \fi
    \hfuzz=0.1pt }%
\newif\if@fixedfloat
\def\@fixedtable{\vskip\intextsep \@fixedfloattrue
    \def\caption{\@ifnextchar[{\f@xedcap{table}}%
      {\f@xedcap{table}[]}}}
\def\@fixedfigure{\vskip\intextsep \@fixedfloattrue
    \def\caption{\@ifnextchar[{\f@xedcap{figure}}%
      {\f@xedcap{figure}[]}}}
\def\f@xedcap#1[#2]#3{\refstepcounter{#1}\def\@tempa{#2}%
  \ifx\@tempa\empty
  \else \addcontentsline{\csname ext@#1\endcsname}{#1}{#2}\fi
    \message{#1\space\csname the#1\endcsname \space (fixed)}%
    \global\@floatcaption={#3}}
\def\calc@fixedspace#1{%
       \@tempdima=\pagegoal
       \@tempdimb=\dp#1
       \advance\@tempdimb \ht#1
       \advance\@tempdima -\pagetotal
       \advance\@tempdima -2\intextsep
         \wlog{pageleft= \the\@tempdima,
           size= \the\@tempdimb }%
       \ifdim\@tempdima>\@tempdimb \else \newpage \fi}
\@ifundefined{thefigure}{\newcounter{figure}}{}
\def\thefigure{\arabic{figure}}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename~\thefigure\figtabdot}
\newif\if@figindent   \@figindentfalse
\def\figindent#1{%
  \global\floatindent #1
  \global\@figindenttrue }
\def\figcapfont{\footnotesize}
\long\def\@makefigcaption#1#2{%
  \message{\figurename\space\thefigure
      \if@kaprotate \space (rotated)\fi }%
  \global\@floatcaption={#2}}
\def\figure{%
   \gdef\cap@type{1}%
   \let\@makecaption\@makefigcaption
   \global\@floatcaption={}%
   \@ifnextchar[{\f@gurewithoptions}{\f@gurewithoptions[tbp]}}%
\def\f@gurewithoptions[#1]{%
  \let\saved@centerline\centerline
  \if H#1\@fixedfigure \else \@float{figure}[#1]\fi
    \@getmaxwidth \if@figindent \@floatcorrect
        \def\centerline##1{##1}\fi
  \setbox\figtabbox\vbox\bgroup }%
\def\endfigure{\egroup
       \@getindent \gdef\cap@type{0}%
       \hfuzz=\floatindent
       \if@kaprotate \@setrotatedfigbox \pagebreak
       \else \@setnotrotatedfigbox \fi
       \let\centerline\saved@centerline
       \if@fixedfloat \vskip\intextsep \@fixedfloatfalse
       \else \end@float \fi
       \hfuzz=0.1pt }%
\@namedef{figure*}{%
    \def\cap@type{1}%
    \let\@makecaption\@makefigcaption
    \global\@floatcaption={}%
    \@ifnextchar[{\df@gurewithoptions}{\df@gurewithoptions[ttp]}}
\def\df@gurewithoptions[#1]{%
  \let\saved@centerline\centerline
  \if H#1 \@fixedfigure \else \@dblfloat{figure}[#1]\fi
    \@getmaxwidth \if@figindent \@floatcorrect
        \def\centerline##1{##1}\fi
     \setbox\figtabbox\vbox\bgroup }%
\@namedef{endfigure*}{\egroup
        \@getindent \gdef\cap@type{0}%
        \hfuzz=\floatindent
        \if@kaprotate \@setrotatedfigbox
        \else \@setnotrotatedfigbox \fi
         \let\centerline\saved@centerline
        \if@fixedfloat \vskip\intextsep \@fixedfloatfalse
        \else \end@dblfloat \fi
        \hfuzz=0.1pt }%
\def\@setnotrotatedfigbox{%
  \setbox4=\hbox to \maxfloatwidth{\vbox{\hsize=\maxfloatwidth
     \unvbox\figtabbox
     \vskip\captionskip
     \@klu@figcaption }}%
      \if@fixedfloat\calc@fixedspace4 \fi
  \noindent\kern \floatindent\box4
}
\def\@setrotatedfigbox{%
     \setbox2\vbox to \hsize{\hsize=\textheight
         \leavevmode
         \vrule width \textheight height 0pt depth 0pt\par
         \vskip \@tabskip
         \hbox to \textheight{\hss\box\figtabbox\hss}%
         \vskip\captionskip
         \hbox to \textheight{\vbox{\@klu@figcaption }}
         \vss
    }\rotl{2}}%
\newcounter{algorithm}
\def\thealgorithm{\arabic{algorithm}}
\def\fps@algorithm{tbp}
\def\ftype@algorithm{4}
\def\ext@algorithm{lof}
\long\def\@makealgocaption#1#2{%
     \hbox to \hsize{\parbox[t]{\hsize}{{\vskip 1ex \tabcapfont
     #1\figtabdot~~#2}}}}
\def\fnum@algorithm{\algorithmname\space \thealgorithm}
\def\algorithm{\let\@makecaption\@makealgocaption
                \@float{algorithm}\footnotesize\obeyspaces\obeylines}
\let\endalgorithm\end@float
\def\subtable{\@ifnextchar[{\@subtable}{\@subtable[alph]}}
\def\@subtable[#1]{\refstepcounter{table}%
  \def\@testoption{arabic}\def\@testparam{#1}%
  \begingroup
  \edef\old@table{\the\c@table}%
  \edef\old@thetable{\thetable}%
  \setcounter{table}{0}%
  \ifx\@testoption\@testparam
     \def\thetable{\old@thetable.\csname #1\endcsname{table}}%
  \else
     \def\thetable{\old@thetable\csname #1\endcsname{table}}%
  \fi}
\def\endsubtable{\setcounter{table}{\old@table}%
  \endgroup \global\@ignoretrue}
\def\subfigure{\@ifnextchar[{\@subfigure}{\@subfigure[alph]}}
\def\@subfigure[#1]{\refstepcounter{figure}%
  \def\@testoption{arabic}\def\@testparam{#1}%
  \begingroup
  \edef\old@figure{\the\c@figure}%
  \edef\old@thefigure{\thefigure}%
  \setcounter{figure}{0}%
  \ifx\@testoption\@testparam
     \def\thefigure{\old@thefigure.\csname #1\endcsname{figure}}%
   \else
     \def\thefigure{\old@thefigure\csname #1\endcsname{figure}}%
   \fi}
\def\endsubfigure{\setcounter{figure}{\old@figure}%
  \endgroup \global\@ignoretrue}

\newif\if@kaprotate \@kaprotatefalse
\def\kaprotate{\global\@kaprotatetrue}
\def\endkaprotate{\global\@kaprotatefalse}

\newdimen\rotdimen
\def\rotstart#1{\special{ps: gsave currentpoint currentpoint translate
    #1 neg exch neg exch translate}}
\def\rotfinish{\special{ps: currentpoint grestore moveto}}
\def\rotl#1{\rotdimen=\ht#1\advance\rotdimen by \dp#1
    \hbox to \rotdimen{\vbox to\wd#1{\vskip \wd#1
    \rotstart{270 rotate}\box #1\vss}\hss}\rotfinish}
\def\rotr#1{\rotdimen=\ht #1\advance\rotdimen by \dp#1
    \hbox to \rotdimen{\vbox to \wd#1{\vskip \wd#1
    \rotstart{90 rotate}\box #1\vss}\hss}\rotfinish}
\def\footnoterule{\kern-3\p@
  \hrule width 3pc
  \kern 2.6\p@}
\long\def\@makefntext#1{\parindent 1em\noindent
 \hbox to 1.5em{\hss\textsuperscript{\@thefnmark}}%
   \hskip0.5em\footnotesize#1}
\def\@makefnmark{\hbox{\textsuperscript{\@thefnmark}}}
\footnotesep 6pt
\skip\footins 10pt plus 4pt minus 2pt
\newcounter{endnote}
\def\theendnote{\arabic{endnote}}
\def\@makeenmark{\hbox{$^{\@theenmark}$}}
\newdimen\endnotesep
\setlength\endnotesep{1pt}
\def\notesname{Notes}% <------ JK
\def\endnotesize{\footnotesize}
\def\endnoteformat{\vskip\endnotesep
     \rightskip\z@ \leftskip\z@
     \parindent=1.8em\leavevmode\llap{\hbox{$^{\@theenmark}$ }}}
\def\endnote{%
   \@ifnextchar[
      {\@xendnote}%
      {\stepcounter{endnote}%
          \xdef\@theenmark{\theendnote}%
          \@endnotemark
          \@endnotetext}}
\long\def\addtoendnotes#1{%
     \if@endnotesopen \else \@openendnotes \fi
     \begingroup
        \newlinechar='40
        \let\protect\string
        \if@filesw \immediate\write\@endnotes{#1}\fi
     \endgroup}
\def\theendnotes{%
  \if@filesw \immediate\closeout\@endnotes \fi
  \global\@endnotesopenfalse
  \begingroup
    \makeatletter
    \def\@doanendnote##1##2>{%
        \def\@theenmark{##1}%
        \par\begingroup
        \endnoteformat}%
    \def\@endanendnote{\par\endgroup}%
    \def\ETC.{\PackageError{klunote}{%
         Some endnotes will be truncated}{%
         Because of memory constraints, LaTeX truncated some\MessageBreak
         long endnotes while writing the auxiliary file.\MessageBreak
         Use a bigger TeX main memory size to avoid this,\MessageBreak
         It is save to continue by pressing <enter>}%
         \def\ETC.{\relax}}%
       \IfFileExists{\jobname.ent}{%
    \endnoteheading
    \endnotesize
    \@input{\jobname.ent}}{}%
  \endgroup }
\def\endnotemark{%
  \@ifnextchar[{\@xendnotemark}%
               {\stepcounter{endnote}%
                \xdef\@theenmark{\theendnote}%
                \@endnotemark}}
\def\endnotetext{%
   \@ifnextchar[{\@xendnotenext}%
                {\xdef\@theenmark{\theendnote}%
                 \@endnotetext}}
\def\endnoteheading{\section*{\notesname
     \imarkboth{\notesname}{\notesname}}\leavevmode\par}
\def\@xendnote[#1]{\begingroup
   \c@endnote=#1\relax
   \xdef\@theenmark{\theendnote}\endgroup
   \@endnotemark\@endnotetext}
\let\@doanendnote=0
\let\@endanendnote=0
\newwrite\@endnotes
\newif\if@endnotesopen \@endnotesopenfalse
\def\@openendnotes{%
      \if@filesw \immediate\openout\@endnotes=\jobname.ent\relax
                 \global\@endnotesopentrue \fi}
\long\def\@endnotetext#1{%
     \if@endnotesopen \else \@openendnotes \fi
     \if@filesw \immediate\write\@endnotes{\@doanendnote{\@theenmark}}\fi
     \begingroup
        \def\next{#1}%
        \newlinechar='40
        \if@filesw \immediate\write\@endnotes{\meaning\next}\fi
     \endgroup
     \if@filesw \immediate\write\@endnotes{\@endanendnote}\fi
     \edef\@currentlabel{\csname p@endnote\endcsname\@theenmark}}
\def\@xendnotemark[#1]{%
    \begingroup
    \c@endnote #1\relax
    \xdef\@theenmark{\theendnote}\endgroup
    \@endnotemark}
\def\@endnotemark{%
   \leavevmode
   \ifhmode \edef\@x@sf{\the\spacefactor}\fi
   \@makeenmark
   \ifhmode\spacefactor\@x@sf\fi\relax}
\def\@xendnotenext[#1]{%
   \begingroup \c@endnote=#1\relax
   \xdef\@theenmark{\theendnote}\endgroup
   \@endnotetext}
\newenvironment{thebibliography}[1]{%
  \sectioncmd*{\refname}\imarkboth{\bibname}{\bibname}%
  \footnotesize
  \message{\refname}
  \def\bibwidthlabel{\releft#1\reright}%
  \list{\kapbib@counter}{\kapbib@list}
  \let\makelabel\@biblabel
  \def\newblock{\hskip .11em plus .33em minus .07em}%
  \sloppy
  \clubpenalty10000
  \widowpenalty10000
  \sfcode`\.=1000\relax
  }{\endlist}
\AtBeginDocument{%
  \def\refname{References}%
  \def\bibname{References}}
\def\i@oldseries{}
\newlength{\bibhang}
\setlength{\bibhang}{14pt}
\newcommand{\redot}{.}
\newcommand{\releft}{}
\newcommand{\reright}{}
\if@numreferences
  \def\coleft{[}
  \def\ccright{]}
\else
  \def\coleft{(}
  \def\ccright{)}
\fi
\def\@cite#1#2{\coleft{#1\if@tempswa , #2\fi}\ccright}
\let\oldcite\cite
\def\numreferences{%
  \typeout{KAP -- Numbered references}%
  \def\kapbib@counter{\arabic{enumiv}}%
  \def\labelsepwidth{1em}%
  \def\kapbib@list{%
    \setlength{\labelsep}{\labelsepwidth}%
    \settowidth{\labelwidth}{\@biblabel{\bibwidthlabel}}%
    \setlength{\leftmargin}{\labelwidth}%
    \addtolength{\leftmargin}{\labelsep}%
    \setlength{\itemindent}{0pt}%
    \setlength{\itemsep}{0pt}%
    \setlength{\parsep}{0pt}%
    \usecounter{enumiv}%
    \let\makelabel\kap@biblabel}%
  \def\@biblabel##1{\hfill\releft##1\redot\reright}%
  \def\@bibitem##1{\item
    \def\@tempa{##1}%
    \ifx\@tempa\empty
      \if@filesw
      \immediate\write\@auxout
      {\string\bibcite{\thearticle \the\value{\@listctr}}%
                        {\the\value{\@listctr}}}%
      \fi
    \else
      \if@filesw
      \immediate\write\@auxout
      {\string\bibcite{\thearticle ##1}{\the\value{\@listctr}}}%
      \fi
    \fi
    \ignorespaces
    }%
  \def\@lbibitem[##1]##2{%
    \def\@biblabel####1{####1}%
    \let\makelabel\@biblabel
    \def\@tempa{##2}%
    \ifx\@tempa\empty
      \item[\@biblabel{\hfill\releft
          \arabic{\@listctr}\redot\reright}]%
      \if@filesw
        {\def\protect####1{\string ####1\space}\immediate
        \write\@auxout{\string\bibcite{\thearticle \the\value{\@listctr}}%
        {\the\value{\@listctr}}}}%
      \fi
    \else
      \item[\@biblabel{\hfill\releft ##1\redot\reright}]%
      \if@filesw
        {\def\protect####1{\string ####1\space}\immediate
        \write\@auxout{\string\bibcite{\thearticle ##2}{##1}}}%
      \fi
    \fi
    \ignorespaces
    }%
  \let\@internalcite\oldcite
  \let\shortcite\@internalcite
  \let\citeauthor\@internalcite
  \let\citeyear\@internalcite
  \let\inlinecite\@internalcite
  \let\opencite\@internalcite
  \let\cite\@internalcite
  \def\citeauthoryear##1##2{}%
\def\@citex[##1]##2{%
  \let\@citea\@empty
  \@cite{\@for\@citeb:=##2\do
    {\@citea\def\@citea{,\penalty\@m\ }%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \edef\gl@citeb{\expandafter\@firstofone\@citeb}%
     \edef\@citeb{\thearticle\expandafter\@firstofone\@citeb}%
     \@ifundefined{b@\@citeb}{%
        \@ifundefined{b@\gl@citeb}{%
            \mbox{\reset@font\bfseries ?}%
            \G@refundefinedtrue
            \@latex@warning
            {Citation `\@citeb' on page \thepage \space undefined}}%
            {\hbox{\csname b@\gl@citeb\endcsname}}}%
         {\hbox{\csname b@\@citeb\endcsname}}%
       }}{##1}}
}
\def\namedreferences{%
  \typeout{KAP -- Named references}%
  \def\@bibitem##1{\item
    \def\@tempa{##1}%
    \ifx\@tempa\empty
      \if@filesw \immediate\write\@auxout{%
        \string\bibcite{\thearticle ??}{??}}\fi
    \else
      \if@filesw \immediate\write\@auxout{%
        \string\bibcite{\thearticle ##1}{??}}\fi
    \fi
    \ignorespaces
    }%
  \def\@lbibitem[##1]##2{\item[\@biblabel{##1}\hfill]%
    \def\@tempa{##2}%
    \stepcounter{\@listctr}%
    \ifx\@tempa\empty
      \if@filesw{\def\protect####1{\string ####1\space}\immediate
       \write\@auxout{\string\bibcite{\thearticle
        \the\value\@listctr}{##1}}}\fi
    \else
      \if@filesw{\def\protect####1{\string ####1\space}\immediate
       \write\@auxout{\string\bibcite{\thearticle ##2}{##1}}}\fi
    \fi
    \ignorespaces
    }%
\def\labelsepwidth{1em}%
\def\kapbib@counter{\relax }%
  \def\kapbib@list{%
    \setlength{\labelsep}{0em}%
    \setlength{\labelwidth}{0pt}%
    \setlength{\itemindent}{-\bibhang}%
    \setlength{\itemsep}{0pt}%
    \setlength{\parsep}{0pt}%
    \usecounter{enumiv}%
    \setlength{\leftmargin}{\bibhang}%
    \i@oldseries
    }%
  \def\@biblabel##1{}%
  \let\@internalcite\oldcite
  \def\cite{\@ifstar{\citeyear}{\klu@cite}}%

  \def\klu@cite{\def\@citeseppen{1000}%
    \def\@cite####1####2{\coleft{####1\if@tempswa , ####2\fi}\ccright}%
    \def\citeauthoryear####1####2{{\rm\i@oldseries ####1, ####2}}\@internalcite }%

  \def\shortcite{\def\@citeseppen{1000}%
    \def\@cite####1####2{\coleft{####1\if@tempswa , ####2\fi}\ccright}%
    \def\citeauthoryear####1####2{{\rm\i@oldseries ####2}}\@internalcite }%

  \def\citeauthor##1{\def\@citeseppen{1000}%
    \def\@cite####1####2{{####1\if@tempswa , ####2\fi}}%
    \def\citeauthoryear####1####2{\rm ####1}\@citedata{##1}}%

  \def\citeyear##1{\def\@citeseppen{1000}%
    \def\@cite####1####2{{####1\if@tempswa , ####2\fi}}%
    \def\citeauthoryear####1####2{{\rm\i@oldseries ####2}}\@citedata{##1}}%

  \def\opencite##1{\citeauthor{##1}, \citeyear{##1}}%

  \def\inlinecite##1{\citeauthor{##1} (\citeyear{##1})}%
\def\@citedata##1{%
    \@tempswafalse%
  \let\@citea\@empty
  \@cite{\@for\@citeb:=##1\do
    {\@citea\def\@citea{,\penalty\@citeseppen\ }%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \edef\gl@citeb{\expandafter\@firstofone\@citeb}%
     \edef\@citeb{\thearticle\expandafter\@firstofone\@citeb}%
     \@ifundefined{b@\@citeb}{%
        \@ifundefined{b@\gl@citeb}{%
            \mbox{\reset@font\bfseries ?}%
            \G@refundefinedtrue
            \@latex@warning
            {Citation `\@citeb' on page \thepage \space undefined}}%
            {\csname b@\gl@citeb\endcsname}}%
         {\csname b@\@citeb\endcsname}}}{}}
\def\@citex[##1]##2{%
  \let\@citea\@empty
  \@cite{\@for\@citeb:=##2\do
    {\@citea\def\@citea{;\penalty\@citeseppen\ }%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \edef\gl@citeb{\expandafter\@firstofone\@citeb}%
     \edef\@citeb{\thearticle\expandafter\@firstofone\@citeb}%
     \@ifundefined{b@\@citeb}{%
        \@ifundefined{b@\gl@citeb}{%
            \mbox{\reset@font\bfseries ?}%
            \G@refundefinedtrue
            \@latex@warning
            {Citation `\@citeb' on page \thepage \space undefined}}%
            {\csname b@\gl@citeb\endcsname}}%
         {\csname b@\@citeb\endcsname}}}{##1}}
\def\citeauthoryear##1##2{\string\citeauthoryear{##1}{##2}}}
%%%%%%%%%%%%%%%%%%%%%%%%%
\if@numreferences
    \numreferences
\else
    \namedreferences
\fi
\def\trivm@th{%
  \ifnum \@itemdepth >0 \topsep\topsepm@th \fi
  \ifnum \@enumdepth >0 \topsep\topsepm@th \fi
  \trivlist}
\def\endtrivm@th{\endtrivlist %\egroup
}
\newdimen\eqnoindent
\setlength{\eqnoindent}{0pt}
\def\varequation#1{$$ \gdef\curr@vareq{#1}}
\def\endvarequation{\eqno \var@eqnnum $$\global\@ignoretrue }
\def\var@eqnnum{\reset@font\normalcolor  (\curr@vareq)}
\def\varleqno{%
   \def\@eqnnum{\hbox to .01\p@{}%
     \rlap{\reset@font\rmfamily\normalcolor
     \hskip -\displaywidth (\theequation)}}%
   \def\var@eqnnum{\hbox to .01\p@{}%
     \rlap{\reset@font\rmfamily\normalcolor
     \hskip -\displaywidth (\curr@vareq)}}%
}%
\def\varfleqn{%
  \newdimen\mathindent
  \mathindent\leftmargini
  \def\varequation##1{%
    \@beginparpenalty\predisplaypenalty
    \@endparpenalty\postdisplaypenalty
    \gdef\curr@vareq{##1}\trivm@th
    \item[]\leavevmode
    \hbox to\linewidth\bgroup $ \displaystyle
    \hskip\mathindent }%
  \def\endvarequation{$\hfil \displaywidth\linewidth
    \ifdim \eqnoindent =\z@
       \llap{\hbox{\var@eqnnum}}%
     \else
       \llap{\hbox to 2pc{\var@eqnnum\hss}\kern \displaywidth
        \kern -\eqnoindent}%
     \fi
     \egroup  \endtrivm@th}%
  \def\[{\relax
          \ifmmode\@badmath
         \else
         \begin{trivm@th}%
           \@beginparpenalty\predisplaypenalty
           \@endparpenalty\postdisplaypenalty
           \item[]\leavevmode
           \hbox to\linewidth\bgroup $\m@th\displaystyle %$
             \hskip\mathindent\bgroup
         \fi}%
  \def\]{\relax
          \ifmmode
                \egroup $\hfil% $
              \egroup
            \end{trivm@th}%
          \else \@badmath
          \fi}%
  \renewenvironment{equation}{%
     \@beginparpenalty\predisplaypenalty
     \@endparpenalty\postdisplaypenalty
     \refstepcounter{equation}%
     \trivm@th
       \item[]\leavevmode
       \hbox to\linewidth\bgroup $\m@th% $
         \displaystyle
         \hskip\mathindent}%%%%%%%
        {$\hfil % $
         \displaywidth\linewidth
    \ifdim \eqnoindent =\z@
       \llap{\hbox{\@eqnnum}}%
     \else
       \llap{\hbox to 2pc{\@eqnnum\hss}\kern \displaywidth
        \kern -\eqnoindent}%
     \fi
       \egroup
     \endtrivm@th}%
  \renewenvironment{eqnarray}{%
    \stepcounter{equation}%
    \def\@currentlabel{\p@equation\theequation}%
    \global\@eqnswtrue\m@th
    \global\@eqcnt\z@
    \tabskip\mathindent
    \let\\=\@eqncr
    \setlength{\abovedisplayskip}{\topsep}%
    \ifvmode
      \addtolength{\abovedisplayskip}{\partopsep}%
    \fi
    \addtolength{\abovedisplayskip}{\parskip}%
    \setlength{\belowdisplayskip}{\abovedisplayskip}%
    \setlength{\belowdisplayshortskip}{\abovedisplayskip}%
    \setlength{\abovedisplayshortskip}{\abovedisplayskip}%
    $$\everycr{}\halign to\linewidth% $$
    \bgroup
      \hskip\@centering
      $\displaystyle\tabskip\z@skip{####}$\@eqnsel&%
      \global\@eqcnt\@ne \hskip \tw@\arraycolsep \hfil${####}$\hfil&%
      \global\@eqcnt\tw@ \hskip \tw@\arraycolsep
        $\displaystyle{####}$\hfil \tabskip\@centering&%
      \global\@eqcnt\thr@@
           \llap \bgroup
          \ifdim \eqnoindent =\z@ \else
         \hbox to 2pc \bgroup \fi
              ####\ifdim \eqnoindent =\z@
              \egroup \else \hss\egroup\kern \displaywidth
        \kern -\eqnoindent\egroup
     \fi \tabskip\z@skip\cr}%
      {\@@eqncr
    \egroup
    \global\advance\c@equation\m@ne$$% $$
    \global\@ignoretrue
    }}
\def\subequation{\@ifnextchar[{\@subequation}{\@subequation[alph]}}
\def\@subequation[#1]{\refstepcounter{equation}%
  \def\@testoption{arabic}%
  \def\@testparam{#1}%
  \edef\old@equation{\the\c@equation}%
  \edef\old@theequation{\theequation}%
  \setcounter{equation}{0}%
  \ifx\@testoption\@testparam
    \def\theequation{\old@theequation.\csname #1\endcsname{equation}}%
  \else
    \def\theequation{\old@theequation\csname #1\endcsname{equation}}%
  \fi}
\def\endsubequation{%
  \setcounter{equation}{\old@equation}%
  \global\@ignoretrue
}
\newif\if@novspace
\let\@thmscase\uppercase
\newdimen\theoremsep
\theoremsep\z@
\def\thmdot{.}
\def\@stylehead{\rm }
\def\@styletext{\em }
\let\@dispcase\relax
\newdimen\dispsep
\dispsep\parindent
\def\dispdot{.}
\def\@disphead{\it }
\def\@disptext{\rm }

\def\pr@@f#1{%
  \par
    \if@novspace \vskip-\lastskip
    \else \addvspace{1\baselineskip
            \@plus 0.5\baselineskip \@minus 0.1\baselineskip}%
    \fi \indent
    {\it #1.\/} \ignorespaces
}
\def\endpr@@f{%
  \par
   \addvspace{1\baselineskip \@plus 0.5\baselineskip \@minus
        0.1\baselineskip}%
    \global\@novspacefalse
}

\def\newproof#1#2{%
  \expandafter\def\csname #1\endcsname{\pr@@f{#2}}%
  \expandafter\def\csname end#1\endcsname{\endpr@@f}}
\newproof{pf}{Proof}

\newenvironment{pf*}[1]{\pr@@f{#1}}{\endpr@@f}
\def\qed{\relax
     \ifmmode
       ~\hfill\Box
     \else
        \unskip\nobreak ~\hfill$\Box$%
      \fi \par}
\newlength\items@ve\newlength\labels@ve
\def\@begintheorem#1#2{%
  \items@ve=\itemindent \labels@ve=\labelsep
  \trivlist
    \global\@novspacetrue \itemindent\theoremsep
     \item[\kern\labelsep
     {\@stylehead\@thmscase{#1}\ #2\thmdot\/}]\ \@styletext
     \itemindent=\items@ve \labelsep=\labels@ve}
\def\@opargbegintheorem#1#2#3{%
      \items@ve=\itemindent \labels@ve=\labelsep
      \trivlist \labelsep\z@
      \global\@novspacetrue \itemindent\theoremsep
      \item[\kern \labelsep {\@stylehead\@thmscase{#1}\ #2\
      (#3). \/}]\ \@styletext
      \itemindent=\items@ve \labelsep=\labels@ve}
\def\@endtheorem{\endtrivlist}
\def\rmtheorem#1{%
    \expandafter\g@addto@macro\csname #1\endcsname{\rmfamily\upshape }%
    }
\def\newdisplay#1{\@ifnextchar[{\@odisp{#1}}{\@ndisp{#1}}}
\def\@ndisp#1#2{%
  \@ifnextchar[{\@xndisp{#1}{#2}}{\@yndisp{#1}{#2}}}
\def\@xndisp#1#2[#3]{\expandafter\@ifdefinable\csname #1\endcsname
  {\@definecounter{#1}\@newctr{#1}[#3]%
      \expandafter\xdef\csname the#1\endcsname{\expandafter\noexpand
        \csname the#3\endcsname \@dispcountersep \@dispcounter{#1}}%
\global\@namedef{#1}{%
  \@disp{#1}{#2}}\global\@namedef{end#1}{\@enddisplay}}}
\def\@yndisp#1#2{\expandafter\@ifdefinable\csname #1\endcsname
{\@definecounter{#1}%
\expandafter\xdef\csname the#1\endcsname{\@dispcounter{#1}}%
\global\@namedef{#1}{%
  \@disp{#1}{#2}}\global\@namedef{end#1}{\@enddisplay}}}
\def\@odisp#1[#2]#3{%
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
  {\expandafter\@ifdefinable\csname #1\endcsname
  {\global\@namedef{the#1}{\@nameuse{the#2}}%
\global\@namedef{#1}{\@disp{#2}{#3}}%
\global\@namedef{end#1}{\@enddisplay}}}}
\def\@disp#1#2{\refstepcounter
    {#1}\@ifnextchar[{\@ydisp{#1}{#2}}{\@xdisp{#1}{#2}}}
\def\@xdisp#1#2{\@begindisplay{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@ydisp#1#2[#3]{\@opargbegindisplay{#2}{\csname
       the#1\endcsname}{#3}\ignorespaces}
\def\@dispcounter#1{\noexpand\arabic{#1}}
\def\@dispcountersep{.}
\def\@begindisplay#1#2{%
    \items@ve=\itemindent \labels@ve=\labelsep
    \trivlist
    \global\@novspacefalse \itemindent\dispsep
        \item[{\@disphead
        \@dispcase{#1}\ #2\dispdot \/}]\@disptext
        \itemindent=\items@ve \labelsep=\labels@ve}
\def\@opargbegindisplay#1#2#3{%
    \items@ve=\itemindent \labels@ve=\labelsep
      \trivlist
      \global\@novspacefalse
      \itemindent \dispsep
      \item[{\@disphead \@dispcase{#1}\ #2\dispdot\
      (\@dispcase{#3})\/}]\@disptext
      \itemindent=\items@ve \labelsep=\labels@ve}
\def\@enddisplay{\endtrivlist}
\if@thms
  \newtheorem{thm}{THEOREM}
  \newtheorem{cor}[thm]{COROLLARY}
  \newtheorem{lem}[thm]{LEMMA}
  \newtheorem{claim}[thm]{CLAIM}
  \newtheorem{conj}[thm]{CONJECTURE}
  \newtheorem{prop}[thm]{PROPOSITION}
  \newtheorem{exer}[thm]{EXERCISE}
  \newtheorem{REM}[thm]{REMARK}
  \newtheorem{prob}[thm]{PROBLEM}
  \newtheorem{alg}{ALGORITHM}
  \rmtheorem{alg}
  \newtheorem{defn}[thm]{DEFINITION}
  \rmtheorem{defn}
  \newtheorem{exmp}[thm]{EXAMPLE}
  \rmtheorem{exmp}
  \newdisplay{crit}{Criterion}
  \newdisplay{rem}{Remark}
  \newdisplay{Note}{Note}
  \newdisplay{summ}{Summary}
  \newdisplay{case}{Case}
\fi
\arraycolsep = 3pt
\@EndKlumathook
\newcommand{\part}{%
  \cleardoublepage
  \thispagestyle{part}%
  \hbox{}\vskip 2in
  \secdef\@part\@spart}
\def\@part[#1]#2{%
  \ifnum \c@secnumdepth >-2\relax
    \refstepcounter{part}%
    \addcontentsline{toc}{part}{\thepart\hspace{1em}#1}%
  \else
    \addcontentsline{toc}{part}{#1}%
  \fi
  \imarkboth{}{}%
  {\centering
    \ifnum \c@secnumdepth >-2\relax
      \huge\bf \partname\ \thepart
      \par
      \vskip 20pt
    \fi
    \Huge \bf #1\par
  }%
  \@endpart
  }

\def\@spart#1{{\centering\Huge \bf #1\par}\@endpart}
\def\@endpart{\vfil\cleardoublepage}
\def\partname{Part}
\let\ps@part\ps@empty

\if@chapterdef

  %
  % Typeset text and number.
  %
  \newcommand{\@makechapterhead}[2]{\vspace*{\Cspaceabove}%
    {\parindent 0pt \hyphenpenalty 10000
     \Cflushstyle \Cnumstyle
     \Chang{#1}%
     \Ctextstyle \Ccase{#2}\par
     \nobreak \Cspaceafter \relax
    }}

  \newcommand{\chapter}{%
    \if@openright
        \cleardoublepage
    \else
       \clearpage
    \fi
    \thispagestyle{chapter}%
    \global\@topnum\z@
    \@afterindentfalse
    \secdef\@chapter\@schapter
    }
  \def\@chapter[#1]#2{%
    \ifnum \c@secnumdepth >\m@ne
      \refstepcounter{chapter}%
      \message{\@chapapp\space\thechapter\chapterdot}%
      \addcontentsline{toc}{chapter}{\protect
        \numberline{\thechapter}#1}%
    \else
      \addcontentsline{toc}{chapter}{#1}%
    \fi
    \chaptermark{#1}%
    \addtocontents{lof}{\protect\addvspace{10pt}}%
    \addtocontents{lot}{\protect\addvspace{10pt}}%
    \@makechapterhead{\thechapter\chapterdot\ }{#2}%
    \@afterheading
    }
  \newcommand{\@schapter}[1]{\@makechapterhead{}{#1} \@afterheading}

  \newcommand{\Chang}[1]{#1}
  \newcommand{\Cspaceabove}{33pt}
  \newcommand{\Cspaceafter}{\vskip 33pt}
  \newcommand{\Cflushstyle}{\centering}
  \newcommand{\Cnumstyle}{\large\rm}
  \newcommand{\Ctextstyle}{}
  \newcommand{\Ccase}[1]{#1}
  \newcommand{\@chapapp}{\chaptername}
  \newcommand{\chapterdot}{.}
  \let\ps@chapter\ps@empty
\fi
\newcommand{\vsecspace}[1]{%
   \if@nobreak\else
     \vskip #1\relax \fi}
\def\Shaveatleast{5\baselineskip}
\def\SShaveatleast{4\baselineskip}
\def\SSShaveatleast{4\baselineskip}
\newcommand{\@haveatleast}[1]{\relax\par \vskip #1
     \penalty 0\vskip -#1 \relax }
\def\@Xsect{%
    \global\@nobreakfalse
    \global\@noskipsectrue
    \everypar{\setbox0\lastbox
      \global\@noskipsecfalse
      \begingroup \@Svsechd \endgroup
      \everypar{}%
     }}
\newcommand{\Forcedhang}[1]{\leavevmode
    \setbox0=\hbox{#1}\hangindent\wd0
    \hangafter=1 \box0 }
\def\contentsname{Table of Contents}%
\def\listfigurename{List of Figures}%
\def\listtablename{List of Tables}%
\def\chaptername{Chapter}%
\def\sectionname{Section}%
\def\appendixname{Appendix}%
\newcommand{\@makesectionhead}[2]{\vsecspace{\Sspaceabove}%
  {\parindent0pt \hyphenpenalty=10000 \baselineskip12pt
   \Sflushstyle \Snumstyle
   \Shang{#1}%
   \Stextstyle \Scase{#2}\par
   \nobreak \Sspaceafter \relax
   }}

\newcommand{\section}{\@haveatleast{\Shaveatleast
    }\@afterindentfalse \secdef\@section\@ssection}

\def\@section[#1]#2{%
  \ifnum \c@secnumdepth >\z@
    \refstepcounter{section}%
    \addcontentsline{toc}{section}{\protect \numberline{\thesection}#1}%
  \else
    \addcontentsline{toc}{section}{#1}%
  \fi
  \sectionmark{#1}%
  \@makesectionhead{\thesection\sectiondot\hskip 0.7em}{#2}%
  \@afterheading
  }

\def\@ssection#1{\@makesectionhead{}{#1}\@afterheading}

\newcommand{\Shang}[1]{\Forcedhang{#1}}
\newcommand{\Sflushstyle}{\centering}
\newcommand{\Snumstyle}{\normalsize\bf}
\newcommand{\Stextstyle}{}
\newcommand{\Sspaceabove}{2\baselineskip plus6pt minus4pt}
\newcommand{\Sspaceafter}{\vskip 1\baselineskip plus3pt minus2pt}
\newcommand{\Scase}[1]{#1}
\newcommand{\sectiondot}{.}
\newcommand{\@makesubsectionhead}[2]{\vsecspace{\SSspaceabove}%
  {\parindent0pt \hyphenpenalty=10000 \baselineskip12pt
   \SSflushstyle \SSnumstyle
   \SShang{#1}%
   \SStextstyle \SScase{#2}\par
   \nobreak \SSspaceafter \relax
   }}

\newcommand{\subsection}{\@haveatleast{\SShaveatleast}%
  \@afterindentfalse \secdef\@subsection\@ssubsection
  }

\def\@subsection[#1]#2{%
  \ifnum \c@secnumdepth >\@ne
    \refstepcounter{subsection}%
    \addcontentsline{toc}{subsection}{\protect
      \numberline{\thesubsection}#1}%
  \else
    \addcontentsline{toc}{subsection}{#1}%
  \fi
  \subsectionmark{#1}
  \@makesubsectionhead{\thesubsection\sectiondot\hskip 0.7em}{#2}%
  \@afterheading
  }
\def\@ssubsection#1{\@makesubsectionhead{}{#1}\@afterheading}

\newcommand{\SShang}[1]{\Forcedhang{#1}}
\newcommand{\SSflushstyle}{\raggedright}
\newcommand{\SSnumstyle}{\normalsize\rm}
\newcommand{\SStextstyle}{\sc}
\newcommand{\SSspaceabove}{1\baselineskip plus3pt minus2pt}
\newcommand{\SSspaceafter}{\vskip .8\baselineskip plus2pt minus2pt}
\newcommand{\SScase}[1]{#1}
\newcommand{\@makesubsubsectionhead}[2]{\vsecspace{\SSSspaceabove}%
  {\parindent0pt \hyphenpenalty=10000 \baselineskip12pt
    \SSSflushstyle \SSSnumstyle
    \SSShang{#1}%
    \SSStextstyle \SSScase{#2}\par
    \nobreak \SSSspaceafter \relax
    }}

\newcommand{\subsubsection}{\@haveatleast{\SSShaveatleast
    }\@afterindentfalse
  \secdef\@subsubsection\@ssubsubsection}
\def\@subsubsection[#1]#2{%
  \ifnum \c@secnumdepth >2
    \refstepcounter{subsubsection}
    \addcontentsline{toc}{subsubsection}{\protect
       \numberline{\thesubsubsection}#1}%
  \else
     \addcontentsline{toc}{subsubsection}{#1}%
  \fi
  \subsubsectionmark{#1}
  \@makesubsubsectionhead{\thesubsubsection\sectiondot\hskip0.7em}{#2}%
  \@afterheading
  }
\def\@ssubsubsection#1{\@makesubsubsectionhead{}{#1}\@afterheading}

\newcommand{\SSShang}[1]{\Forcedhang{#1}}
\newcommand{\SSSflushstyle}{\raggedright}
\newcommand{\SSSnumstyle}{\normalsize\rm}
\newcommand{\SSStextstyle}{\it}
\newcommand{\SSSspaceabove}{1\baselineskip plus3pt minus2pt}
\newcommand{\SSSspaceafter}{\vskip 1sp}
\newcommand{\SSScase}[1]{#1}
\newcommand{\@makeparagraphhead}[2]{%
    \vsecspace{\Pspaceabove }%
 \def\@Svsechd{%
    {\Pflushstyle \Pnumstyle
      \Phang{#1}%
      \Ptextstyle \Pcase{#2}%
      \Pspaceafter \relax }}\@Xsect
     }

\newcommand{\paragraph}{\par \@afterindentfalse
  \secdef\@paragraph\@sparagraph }

\def\@paragraph[#1]#2{%
  \ifnum \c@secnumdepth >3
    \refstepcounter{paragraph}%
    \addcontentsline{toc}{paragraph}{\protect
       \numberline{\theparagraph}#1}%
  \else
    \addcontentsline{toc}{paragraph}{#1}%
  \fi
  \paragraphmark{#1}%
  \@makeparagraphhead{\theparagraph\sectiondot\hskip 0.7em}{#2}%
  }
\def\@sparagraph#1{\@makeparagraphhead{}{#1}}

\newcommand{\Pspaceabove}{1\baselineskip plus3pt minus2pt}
\newcommand{\Phang}[1]{#1}
\newcommand{\Pflushstyle}{}
\newcommand{\Pnumstyle}{\normalsize\rm}
\newcommand{\Ptextstyle}{\it}
\newcommand{\Pcase}[1]{#1}
\newcommand{\Pspaceafter}{\hskip 1em}
\newcommand{\@makesubparagraphhead}[2]{%
     \vskip \SPspaceabove
 \def\@Svsechd{%
    {\SPflushstyle \SPnumstyle
      \SPhang{#1}%
      \SPtextstyle \SPcase{#2}%
      \SPspaceafter \relax}}\@Xsect
     }
\newcommand{\subparagraph}{\par\@afterindentfalse
  \secdef\@subparagraph\@ssubparagraph }

\def\@subparagraph[#1]#2{%
  \ifnum \c@secnumdepth >4
    \refstepcounter{subparagraph}%
    \addcontentsline{toc}{subparagraph}{\protect
       \numberline{\thesubparagraph}#1}%
  \else
    \addcontentsline{toc}{subparagraph}{#1}%
  \fi
  \paragraphmark{#1}%
  \@makesubparagraphhead{\thesubparagraph\sectiondot\hskip 0.7em}{#2}%
  }
\def\@ssubparagraph#1{\@makesubparagraphhead{}{#1}}

\newcommand{\SPspaceabove}{1\baselineskip plus3pt minus2pt}
\newcommand{\SPhang}[1]{}
\newcommand{\SPflushstyle}{}
\newcommand{\SPnumstyle}{\normalsize\rm}
\newcommand{\SPtextstyle}{\it}
\newcommand{\SPcase}[1]{#1}
\newcommand{\SPspaceafter}{\hskip 1em}
\newcounter{part}
\renewcommand{\thepart}{\Roman{part}}
\if@chapterdef
  \newcounter{chapter}
  \renewcommand{\thechapter}{\arabic{chapter}}
  \newcounter{section}[chapter]
  \renewcommand{\thesection}{\thechapter.\arabic{section}}
\else
  \newcounter{section}
  \renewcommand{\thesection}{\arabic{section}}
\fi
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\newcounter{subparagraph}[paragraph]
\renewcommand{\thesubsection}{\thesection.\arabic{subsection}}
\renewcommand{\thesubsubsection}{\thesubsection.\arabic{subsubsection}}
\renewcommand{\theparagraph}{\thesubsubsection.\arabic{paragraph}}
\renewcommand{\thesubparagraph}{\theparagraph.\arabic{subparagraph}}
\def\@pnumwidth{1.55em}
\def\@tocrmarg{2.55em}
\def\@dotsep{10000}

\setcounter{tocdepth}{2}
\setcounter{secnumdepth}{4}
\def\tableofcontents{\sectioncmd *{\contentsname}%
  \imarkboth{\contentsname}{\contentsname}%
  \message{\contentsname}%
  \@starttoc{toc}\newpage}
\def\listoffigures{\sectioncmd *{\listfigurename}\imarkboth
  {\listfigurename}{\listfigurename}%
  \message{\listfigurename}%
  \@starttoc{lof}}
\def\listoftables{\sectioncmd *{\listtablename}\imarkboth
  {\listtablename}{\listtablename}%
  \message{\listtablename}%
  \@starttoc{lot}}

\def\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\let\l@table\l@figure

\def\l@part#1#2{%
  \addpenalty{-\@highpenalty}
  \addvspace{2.25em plus 1pt}
  \begingroup
     \@tempdima 3em
     \parindent \z@ \rightskip \@pnumwidth
     \parfillskip -\@pnumwidth
     {\large \bf
       \leavevmode
       #1\hfil \hbox to\@pnumwidth{\hss #2}}\par
     \nobreak
     \global\@nobreaktrue
     \everypar{\global\@nobreakfalse\everypar{}}
   \endgroup
   }

\def\l@chapter#1#2{\addpenalty{-\@highpenalty}
   \vskip 1.0em plus 1pt
   \@tempdima 1.5em
   \begingroup
     \parindent \z@ \rightskip \@pnumwidth
     \parfillskip -\@pnumwidth
     \bf
     \leavevmode
     \advance\leftskip\@tempdima
     \hskip -\leftskip
     #1\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss #2}\par
     \penalty\@highpenalty
   \endgroup
   }

\def\l@section{\@dottedtocline{1}{1.5em}{2.3em}}
\def\l@subsection{\@dottedtocline{2}{3.8em}{3.2em}}
\def\l@subsubsection{\@dottedtocline{3}{7.0em}{4.1em}}
\def\l@paragraph{\@dottedtocline{4}{10em}{5em}}
\def\l@subparagraph{\@dottedtocline{5}{12em}{6em}}
\newif\if@mainmatter \@mainmattertrue
\if@chapterdef
  \newcommand{\appendix}{\par
    \@mainmatterfalse
    \setcounter{chapter}{0}%
    \setcounter{section}{0}%
    \renewcommand{\thechapter}{\Alph{chapter}}%
    \renewcommand{\@chapapp}{\appendixname}%
    \message{\appendixname}%
    }
\else
  \newcommand{\appendix}{\par
    \section*{Appendix}%
    \setcounter{section}{0}%
    \setcounter{subsection}{0}%
    \renewcommand{\thesection}{\Alph{section}}%
    \message{\appendixname}%
    }
\fi

\newenvironment{theindex}{%
  \columnseprule \z@
  \columnsep \indexsep
  \if@chapterdef
    \twocolumn[\@makechapterhead{}{\indexname}]
    \addcontentsline{toc}{chapter}{\indexname}%
  \else
    \twocolumn[\@makesectionhead{}{\indexname}]
    \addcontentsline{toc}{section}{\indexname}%
  \fi
  \imarkboth{\indexname}{\indexname}%
  \message{\indexname}%
  \thispagestyle{index}%
  \parindent\z@
  \parskip\z@ plus .3pt\relax
  \let\item\@idxitem \indexfont
  }{\onecolumn}
\def\indexfont{\footnotesize}
\let\ps@index\ps@empty
\def\@idxitem{\par\hangindent 36pt}
\def\subitem{\par\hangindent 36pt \hspace*{12pt}}
\def\subsubitem{\par\hangindent 36pt \hspace*{24pt}}
\def\indexspace{\par \vskip 10pt plus 5pt minus 3pt\relax}
\def\indexsep{24pt}





\@kaplisttrue

\AtBeginDocument{\let\sectioncmd\section}
\AtBeginDocument{\let\imarkboth\@gobbletwo}

\def\@date{\vskip \afterdateskip } % no default dates

\renewcommand{\fnum@figure}{{\itshape\figurename~\thefigure\figtabdot\/}}
\renewcommand{\thetable}{\Roman{table}}
\indentedcaptions

\def\Uppercase#1{#1}
\setlength\textheight{559pt}
\setlength\textwidth{28pc}
\setlength\marginparwidth{0pt}
\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}
\@lowpenalty 51
\@medpenalty 151
\@highpenalty 301
\@beginparpenalty -\@lowpenalty
\@endparpenalty -\@lowpenalty
\@itempenalty -\@lowpenalty
\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\providecommand{\cal}{\protect\pcal}
\newcommand{\pcal}{\@fontswitch{\relax}{\mathcal}}
\providecommand{\mit}{\protect\pmit}
\newcommand{\pmit}{\@fontswitch{\relax}{\mathnormal}}
\setlength\tabbingsep{\labelsep}
\clubpenalty=10000
\widowpenalty=10000
%%%%%%%
\def\kapmathindent{14pt}
\pagestyle{headings}
\pagenumbering{arabic}
\frenchspacing
\endinput
%%
%% End of file `kluwer.cls'.
