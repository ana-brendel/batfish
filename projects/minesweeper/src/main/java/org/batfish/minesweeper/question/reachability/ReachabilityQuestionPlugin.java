package org.batfish.minesweeper.question.reachability;

import com.google.auto.service.AutoService;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;

/** QuestionPlugin for {@link ReachabilityQuestion}. */
@AutoService(Plugin.class)
public final class ReachabilityQuestionPlugin extends QuestionPlugin {
  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new ReachabilityAnswerer((ReachabilityQuestion) question, batfish);
  }

  @Override
  protected Question createQuestion() {
    return new ReachabilityQuestion();
  }
}
