use std::fs::File;
use std::path::Path;
use std::io::prelude::*;
use std::io;
use std::fmt;
use std::cmp;
use std::fmt::Formatter;
use std::ops::{Add, Sub};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Pos {
    pos: usize
}
impl Pos {
    pub fn new(pos: usize) -> Pos {
        Pos{ pos: pos }
    }
}
impl Add<usize> for Pos {
    type Output = Pos;
    fn add(self, other: usize) -> Pos {
        Pos::new(self.pos + other)
    }
}
impl Add<Pos> for Pos {
    type Output = Pos;
    fn add(self, other: Pos) -> Pos {
        Pos::new(self.pos + other.pos)
    }
}
impl Sub<usize> for Pos {
    type Output = Pos;
     fn sub(self, other: usize) -> Pos {
        Pos::new(self.pos - other)
    }
}
impl Sub<Pos> for Pos {
    type Output = usize;
    fn sub(self, other: Pos) -> usize {
        self.pos - other.pos
    }
}


#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Debug)]
pub struct Loc {
    line: usize,
    col: usize
}
impl Loc {
    // The tales of my death were greatly exaggerated.
    #[allow(dead_code)]
    fn new(line: usize, col: usize) -> Loc {
        Loc{ line: line, col: col }
    }
}
impl fmt::Display for Loc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}


#[derive(Clone, Copy)]
pub struct Span<'a> {
    source: &'a SourceFile,
    start: Pos,
    end: Pos
}
impl<'a> Add<Span<'a>> for Span<'a> {
    type Output = Span<'a>;
    fn add(self, other: Span<'a>) -> Span<'a> {
        if self.source != other.source {
            panic!("Attempted to combine two source locations from different files.")
        }
        let start = cmp::min(self.start, other.start);
        let end   = cmp::max(self.end,   other.end  );
        Span{
            source: self.source,
            start: start,
            end: end
        }
    }
}
impl<'a> Span<'a> {

    pub fn new(source: &'a SourceFile, start: Pos, end: Pos) -> Span<'a> {
        Span{
            source: source,
            start: start,
            end: end
        }
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn as_str(&self) -> &'a str {
        &self.source.text[self.start.pos .. self.end.pos]
    }
}

impl<'a> fmt::Display for Span<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &self.source.text[self.start.pos .. self.end.pos])
    }
}
impl<'a> fmt::Debug for Span<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &self.source.text[self.start.pos .. self.end.pos])
    }
}

impl<'a> Span<'a> {
    pub fn preview(&self, preview_len: usize) -> String {
        let preview =
            if self.start + preview_len < self.end {
                self.source.text[
                    self.start.pos ..
                        self.start.pos + preview_len].to_string()
                    + "..."
            } else {
                self.source.text[self.start.pos .. self.end.pos].to_string()
            };
        let start = self.source.pos_to_loc(self.start);
        let end   = self.source.pos_to_loc(self.end);
        format!("{}, at {}-{} `{}`",
                self.source.filename, start, end, preview)
    }
}



pub trait AsSpan<'a> {
    fn span(&self) -> Span<'a>;
}



pub struct SourceFile {
    pub filename: String,
    pub text: String,
    line_splits: Vec<Pos>
}

impl SourceFile {

    pub fn open<P: AsRef<Path>>(path: P) -> Result<SourceFile, io::Error> {
        let mut file = try!(File::open(path.as_ref()));
        let mut contents = String::new();
        try!(file.read_to_string(&mut contents));
        let filename = path.as_ref().to_str().unwrap().to_string();
        Ok(SourceFile::new(filename, contents))
    }

    pub fn open_stdin() -> Result<SourceFile, io::Error> {
        let mut contents = String::new();
        while let Ok(n) = io::stdin().read_line(&mut contents) {
            if n == 0 { break; }
        }
        Ok(SourceFile::new(String::from("stdin"), contents))
    }

    pub fn new(filename: String, text: String) -> SourceFile {
        let mut split = 0;
        let mut line_splits = vec!(Pos::new(0));
        for line in text.lines() {
            split = split + line.len() + 1; // account for newline
            line_splits.push(Pos::new(split));
        }
        SourceFile{
            filename: filename,
            text: text,
            line_splits: line_splits
        }
    }

    pub fn from_str(text: &str) -> SourceFile {
        SourceFile::new(String::from("[Inline String]"), String::from(text))
    }

    pub fn pos_to_loc(&self, pos: Pos) -> Loc {
        let res = self.line_splits.binary_search(&pos);
        match res {
            Ok(line) => Loc{
                line: line + 1,
                col: 0
            },
            Err(line) => Loc{
                line: line,
                col: pos - self.line_splits[line - 1]
            }
        }
    }
}
impl PartialEq for SourceFile {
    fn eq(&self, other: &SourceFile) -> bool {
        self.filename == other.filename
    }
}
impl Eq for SourceFile {}


#[cfg(test)]
mod tests {
    use super::SourceFile;
    use super::Pos;
    use super::Loc;
    use super::Span;

    fn mk_srcfile() -> SourceFile {
        SourceFile::new("FILENAME".to_string(),
                        "abc\n\nde".to_string())
    }

    #[test]
    fn test_pos_to_loc() {
        let src = mk_srcfile();
        assert_eq!(src.pos_to_loc(Pos::new(0)), Loc::new(1, 0));
        assert_eq!(src.pos_to_loc(Pos::new(1)), Loc::new(1, 1));
        assert_eq!(src.pos_to_loc(Pos::new(2)), Loc::new(1, 2));
        assert_eq!(src.pos_to_loc(Pos::new(3)), Loc::new(1, 3));
        assert_eq!(src.pos_to_loc(Pos::new(4)), Loc::new(2, 0));
        assert_eq!(src.pos_to_loc(Pos::new(5)), Loc::new(3, 0));
        assert_eq!(src.pos_to_loc(Pos::new(6)), Loc::new(3, 1));
        assert_eq!(src.pos_to_loc(Pos::new(7)), Loc::new(3, 2));
    }

    #[test]
    fn test_write_span() {
        let src = mk_srcfile();
        let span = Span::new(&src, Pos::new(1), Pos::new(5)); // b..d
        let output = span.preview(40);
        assert_eq!(output, "FILENAME, at 1:1-3:0 `bc\n\n`");
    }
}
