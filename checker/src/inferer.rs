use Ty;

#[derive(Eq, Debug)]
pub struct Constraint {
    left: Ty,
    right: Ty,
}
