/*-
 * #%L
 * DL Library
 * %%
 * Copyright (C) 2020 Francesco Kriegel
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package de.tudresden.inf.lat.dllibrary

import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.util.OWLObjectDuplicator
import org.semanticweb.owlapi.apibinding.OWLManager

object OWLAPI {

  implicit class CloneableOWLClassExpression(val classExpression: OWLClassExpression) extends Cloneable {

    override def clone(): OWLClassExpression = {
      new OWLObjectDuplicator(OWLManager.getOWLDataFactory).duplicateObject(classExpression).asInstanceOf[OWLClassExpression]
    }

  }

}
