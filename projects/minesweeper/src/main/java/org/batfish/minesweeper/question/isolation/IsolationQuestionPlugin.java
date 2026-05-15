package org.batfish.minesweeper.question.isolation;

import com.google.auto.service.AutoService;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.questions.Question;

import org.batfish.question.QuestionPlugin;

/** QuestionPlugin for {@link IsolationQuestion}. */
@AutoService(Plugin.class)
public final class IsolationQuestionPlugin extends QuestionPlugin {
  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new IsolationAnswerer((IsolationQuestion) question, batfish);
  }

  @Override
  protected Question createQuestion() {
    return new IsolationQuestion();
  }
}
