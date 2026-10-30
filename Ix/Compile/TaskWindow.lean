module

public import Init.Data.Array.Basic
public import Init.Task

public section

namespace Ix.Compile.TaskWindow

/-- Wait with synchronous continuations, then queue the computation once.
The waits carry only completion tokens; a dependency edge never queues a
worker whose only job is waiting for another worker. -/
def afterAll (waits : List (Task Unit)) (compute : Unit → α) : Task α :=
  match waits with
  | [] => Task.spawn compute
  | first :: rest => first.bind (sync := true) fun _ => afterAll rest compute

theorem afterAll_get (waits : List (Task Unit)) (compute : Unit → α) :
    (afterAll waits compute).get = compute () := by
  induction waits with
  | nil => rfl
  | cons first rest ih => exact ih

/-- A bounded group releases one token after all of its results are ready. -/
def token (tasks : List (Task α)) : Task Unit :=
  match tasks with
  | [] => Task.pure ()
  | first :: rest => first.bind (sync := true) fun _ => token rest

theorem token_get (tasks : List (Task α)) : (token tasks).get = () := by
  induction tasks with
  | nil => rfl
  | cons first rest ih => exact ih

/-- Keep only a task's completion when its value is no longer needed. -/
def completed (task : Task α) : Task Unit :=
  task.map (fun _ => ()) (sync := true)

theorem completed_get (task : Task α) : (completed task).get = () := rfl

/-- Return the supplied value after completion. Observing the mapped task's
value keeps the wait in generated code; an unused `Task.get` can be removed.
Use a compact plan for intermediate handoffs, keeping live driver maps out
of the continuation. -/
def finish (completion : Task Unit) (value : α) : α :=
  (completion.map (fun _ => value) (sync := true)).get

theorem finish_eq (completion : Task Unit) (value : α) : finish completion value = value := by
  unfold finish
  rfl

end Ix.Compile.TaskWindow
