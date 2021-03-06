/** Ownership and borrowing á lá Rust.

    <ul>
    <li> TODO Move to typecons_ex.

    <li> TODO Override all members with write checks. See http://forum.dlang.org/post/mailman.63.1478697690.3405.digitalmars-d-learn@puremagic.com

    <li> TODO Perhaps disable all checking (and unittests) in release mode (when
    debug is not active), but preserve overloads sliceRO and sliceRW. If not use
    `enforce` instead.

    <li> TODO Implement and use trait `hasUnsafeSlicing`

    <li> TODO Add WriteBorrowedPointer, ReadBorrowedPointer to wrap `ptr` access to Container

    <li> TODO Is sliceRW and sliceRO good names?

    <li> TODO can we make the `_range` member non-visible but the alias this
    public in ReadBorrowed and WriteBorrowed

    </ul>
 */
module borrown;

public import owned;
public import borrowed;
