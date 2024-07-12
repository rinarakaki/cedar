// Tests that trailing spaces are correctly removed at the end of comment lines.
// Be careful and look closely if this test case starts failing. Be sure that
// the output does not contains any trailing whitespace at the end of comments.

// There is a space at the end of this line 
permit (principal, action, resource);

// No space here
// But there is one here 
permit (principal, action, resource);

// No space here
 // Leading space before this comment (that we don't preserve).
// A tab character here:	
permit (principal, action, resource);

permit (principal, // Trailing comment Space 
// Leading comment Space 
// Leading comment Space 
// Leading comment Space 
action, resource);

// end of file comment with space 
// on these lines 
// 
