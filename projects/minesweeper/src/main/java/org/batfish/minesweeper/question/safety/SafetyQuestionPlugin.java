package org.batfish.minesweeper.question.safety;

import com.google.auto.service.AutoService;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.questions.Question;

import org.batfish.question.QuestionPlugin;

/** QuestionPlugin for {@link SafetyQuestion}. */
@AutoService(Plugin.class)
public final class SafetyQuestionPlugin extends QuestionPlugin {
    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new SafetyAnswerer((SafetyQuestion) question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new SafetyQuestion();
    }
}